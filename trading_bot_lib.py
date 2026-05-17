# trading_bot_15m_candle_signal.py
# =============================================================================
#  BOT GIAO DỊCH FUTURES - TÍN HIỆU 2 NẾN 15 PHÚT (KHỐI LƯỢNG)
#  - Vào lệnh: so sánh volume nến trước và nến hiện tại
#      * Nếu vol_prev > vol_curr → vào NGƯỢC hướng nến hiện tại
#      * Nếu vol_prev <= vol_curr → vào CÙNG hướng nến hiện tại
#  - Thoát lệnh: khi một nến 15 phút mới đóng và tín hiệu của nến đó
#    ngược với hướng vị thế đang giữ → đóng lệnh.
#  - Không dùng TP/SL, không ROI trigger, không pyramiding.
#  - Kết hợp cân bằng số lượng lệnh BUY/SELL toàn cục.
# =============================================================================

import json
import hmac
import hashlib
import time
import threading
import urllib.request
import urllib.parse
import numpy as np
import websocket
import logging
import requests
import os
import math
import traceback
import random
import queue
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor
from collections import defaultdict
import ssl
import html
import sys
from typing import Optional, List, Dict, Any, Tuple, Callable

# ========== CẤU HÌNH & HẰNG SỐ ==========
_BINANCE_LAST_REQUEST_TIME = 0
_BINANCE_RATE_LOCK = threading.RLock()
_BINANCE_MIN_INTERVAL = 0.2

_SYMBOL_BLACKLIST = {'BTCUSDT', 'BTCUSDC','ETHUSDT','ETHUSDC'}

# ========== CACHE COIN TẬP TRUNG ==========
class CoinCache:
    def __init__(self):
        self._data: List[Dict] = []
        self._last_volume_update: float = 0
        self._last_price_update: float = 0
        self._lock = threading.RLock()
        self._volume_cache_ttl = 6 * 3600
        self._price_cache_ttl = 300
        self._refresh_interval = 300

    def get_data(self) -> List[Dict]:
        with self._lock:
            return [coin.copy() for coin in self._data]

    def update_data(self, new_data: List[Dict]):
        with self._lock:
            self._data = new_data

    def update_volume_time(self):
        with self._lock:
            self._last_volume_update = time.time()

    def update_price_time(self):
        with self._lock:
            self._last_price_update = time.time()

    def get_stats(self) -> Dict:
        with self._lock:
            return {
                'count': len(self._data),
                'last_volume_update': self._last_volume_update,
                'last_price_update': self._last_price_update,
                'volume_cache_ttl': self._volume_cache_ttl,
                'price_cache_ttl': self._price_cache_ttl,
                'refresh_interval': self._refresh_interval,
            }

    def need_refresh(self) -> bool:
        with self._lock:
            return time.time() - self._last_price_update > self._refresh_interval

_COINS_CACHE = CoinCache()

# ========== CẤU HÌNH LỌC RIÊNG CHO MUA VÀ BÁN ==========
class BalanceConfig:
    def __init__(self):
        self._config = {
            "max_price_buy": float('inf'),
            "max_volume_buy": float('inf'),
            "min_price_sell": 0.0,
            "min_volume_sell": 0.0,
            "min_leverage": 10,
            "sort_by_volume": True,
        }
        self._lock = threading.RLock()

    def get(self, key: str, default=None):
        with self._lock:
            return self._config.get(key, default)

    def get_all(self) -> Dict:
        with self._lock:
            return self._config.copy()

    def update(self, **kwargs):
        with self._lock:
            for k, v in kwargs.items():
                if v is not None:
                    self._config[k] = v

_BALANCE_CONFIG = BalanceConfig()

# ========== QUẢN LÝ HƯỚNG TOÀN CỤC ==========
class GlobalSideCoordinator:
    def __init__(self):
        self._lock = threading.RLock()
        self.last_global_check = 0
        self.global_buy_count = 0
        self.global_sell_count = 0
        self.next_global_side = None
        self.check_interval = 30

    def update_global_counts(self, api_key, api_secret):
        with self._lock:
            if time.time() - self.last_global_check < self.check_interval:
                return self.next_global_side

        try:
            positions = get_positions(api_key=api_key, api_secret=api_secret)
            buy_count = 0
            sell_count = 0
            for pos in positions:
                amt = float(pos.get('positionAmt', 0))
                if amt > 0:
                    buy_count += 1
                elif amt < 0:
                    sell_count += 1

            with self._lock:
                self.global_buy_count = buy_count
                self.global_sell_count = sell_count
                if buy_count > sell_count:
                    self.next_global_side = "SELL"
                elif sell_count > buy_count:
                    self.next_global_side = "BUY"
                else:
                    self.next_global_side = random.choice(["BUY", "SELL"])
                self.last_global_check = time.time()
                logger.info(f"🌍 Số lượng vị thế toàn cục: BUY={buy_count}, SELL={sell_count} → Ưu tiên: {self.next_global_side}")
                return self.next_global_side
        except Exception as e:
            logger.error(f"❌ Lỗi cập nhật số lượng toàn cục: {str(e)}")
            with self._lock:
                self.next_global_side = random.choice(["BUY", "SELL"])
                return self.next_global_side

    def get_next_side(self, api_key, api_secret):
        return self.update_global_counts(api_key, api_secret)

# ========== HÀM TIỆN ÍCH ==========
def setup_logging():
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(module)s - %(message)s',
        handlers=[logging.StreamHandler(), logging.FileHandler('bot_errors.log')]
    )
    return logging.getLogger()

logger = setup_logging()

def escape_html(text):
    if not text: return text
    return html.escape(text)

def send_telegram(message, chat_id=None, reply_markup=None, bot_token=None, default_chat_id=None):
    if not bot_token or not (chat_id or default_chat_id):
        return

    url = f"https://api.telegram.org/bot{bot_token}/sendMessage"
    safe_message = escape_html(message)

    payload = {"chat_id": chat_id or default_chat_id, "text": safe_message, "parse_mode": "HTML"}
    if reply_markup:
        payload["reply_markup"] = json.dumps(reply_markup)

    try:
        response = requests.post(url, json=payload, timeout=15)
        if response.status_code != 200:
            logger.error(f"Lỗi Telegram ({response.status_code}): {response.text}")
    except Exception as e:
        logger.error(f"Lỗi kết nối Telegram: {str(e)}")

# ========== HÀM TẠO BÀN PHÍM ==========
def create_main_menu():
    return {
        "keyboard": [
            [{"text": "📊 Danh sách Bot"}, {"text": "📊 Thống kê"}],
            [{"text": "➕ Thêm Bot"}, {"text": "⛔ Dừng Bot"}],
            [{"text": "⛔ Quản lý Coin"}, {"text": "📈 Vị thế"}],
            [{"text": "💰 Số dư"}, {"text": "⚙️ Cấu hình"}],
            [{"text": "🎯 Chiến lược"}, {"text": "⚖️ Cân bằng lệnh"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": False
    }

def create_cancel_keyboard():
    return {"keyboard": [[{"text": "❌ Hủy bỏ"}]], "resize_keyboard": True, "one_time_keyboard": True}

def create_bot_count_keyboard():
    return {
        "keyboard": [
            [{"text": "1"}, {"text": "3"}, {"text": "5"}],
            [{"text": "10"}, {"text": "20"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_bot_mode_keyboard():
    return {
        "keyboard": [
            [{"text": "🤖 Bot Tĩnh - Coin cụ thể"}, {"text": "🔄 Bot Động - Tự tìm coin"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_symbols_keyboard():
    try:
        coins = get_coins_with_info()
        coins_sorted = sorted(coins, key=lambda x: x['volume'], reverse=True)[:12]
        symbols = [coin['symbol'] for coin in coins_sorted if coin['volume'] > 0]
        if not symbols:
            symbols = ["BNBUSDT", "ADAUSDT", "DOGEUSDT", "XRPUSDT", "DOTUSDT", "LINKUSDT", "SOLUSDT", "MATICUSDT"]
    except:
        symbols = ["BNBUSDT", "ADAUSDT", "DOGEUSDT", "XRPUSDT", "DOTUSDT", "LINKUSDT", "SOLUSDT", "MATICUSDT"]

    keyboard = []
    row = []
    for symbol in symbols:
        row.append({"text": symbol})
        if len(row) == 3:
            keyboard.append(row)
            row = []
    if row:
        keyboard.append(row)
    keyboard.append([{"text": "❌ Hủy bỏ"}])

    return {"keyboard": keyboard, "resize_keyboard": True, "one_time_keyboard": True}

def create_leverage_keyboard():
    leverages = ["3", "5", "10", "15", "20", "25", "50", "75", "100"]
    keyboard = []
    row = []
    for lev in leverages:
        row.append({"text": f"{lev}x"})
        if len(row) == 3:
            keyboard.append(row)
            row = []
    if row:
        keyboard.append(row)
    keyboard.append([{"text": "❌ Hủy bỏ"}])
    return {"keyboard": keyboard, "resize_keyboard": True, "one_time_keyboard": True}

def create_percent_keyboard():
    return {
        "keyboard": [
            [{"text": "1"}, {"text": "3"}, {"text": "5"}, {"text": "10"}],
            [{"text": "15"}, {"text": "20"}, {"text": "25"}, {"text": "50"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_balance_config_keyboard():
    return {
        "keyboard": [
            [{"text": "⚖️ Bật cân bằng lệnh"}, {"text": "⚖️ Tắt cân bằng lệnh"}],
            [{"text": "📊 Xem cấu hình cân bằng"}, {"text": "🔄 Làm mới cache"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_max_price_buy_keyboard():
    return {
        "keyboard": [
            [{"text": "1.0"}, {"text": "2.0"}, {"text": "5.0"}],
            [{"text": "10.0"}, {"text": "20.0"}, {"text": "50.0"}],
            [{"text": "❌ Bỏ qua"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": True
    }

def create_max_volume_buy_keyboard():
    return {
        "keyboard": [
            [{"text": "1000000"}, {"text": "5000000"}, {"text": "10000000"}],
            [{"text": "50000000"}, {"text": "100000000"}, {"text": "500000000"}],
            [{"text": "❌ Bỏ qua"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": True
    }

def create_min_price_sell_keyboard():
    return {
        "keyboard": [
            [{"text": "10"}, {"text": "50"}, {"text": "100"}],
            [{"text": "500"}, {"text": "1000"}, {"text": "5000"}],
            [{"text": "❌ Bỏ qua"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": True
    }

def create_min_volume_sell_keyboard():
    return {
        "keyboard": [
            [{"text": "1000000"}, {"text": "5000000"}, {"text": "10000000"}],
            [{"text": "50000000"}, {"text": "100000000"}, {"text": "500000000"}],
            [{"text": "❌ Bỏ qua"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": True
    }

# ========== HÀM API BINANCE CẢI TIẾN ==========
def _wait_for_rate_limit():
    global _BINANCE_LAST_REQUEST_TIME
    with _BINANCE_RATE_LOCK:
        now = time.time()
        delta = now - _BINANCE_LAST_REQUEST_TIME
        if delta < _BINANCE_MIN_INTERVAL:
            time.sleep(_BINANCE_MIN_INTERVAL - delta)
        _BINANCE_LAST_REQUEST_TIME = time.time()

def sign(query, api_secret):
    try:
        return hmac.new(api_secret.encode(), query.encode(), hashlib.sha256).hexdigest()
    except Exception as e:
        logger.error(f"Lỗi ký: {str(e)}")
        return ""

def binance_api_request(url, method='GET', params=None, headers=None):
    max_retries = 3
    base_url = url
    retryable_codes = {429, 418, 500, 502, 503, 504}
    retryable_errors = ('Timeout', 'ConnectionError', 'BadStatusLine', 'URLError')

    for attempt in range(max_retries):
        try:
            _wait_for_rate_limit()
            url = base_url

            if headers is None: headers = {}
            if 'User-Agent' not in headers:
                headers['User-Agent'] = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'

            if method.upper() == 'GET':
                if params:
                    query = urllib.parse.urlencode(params)
                    url = f"{url}?{query}"
                req = urllib.request.Request(url, headers=headers)
            else:
                data = urllib.parse.urlencode(params).encode() if params else None
                req = urllib.request.Request(url, data=data, headers=headers, method=method)

            with urllib.request.urlopen(req, timeout=15) as response:
                if response.status == 200:
                    return json.loads(response.read().decode())
                else:
                    error_content = response.read().decode()
                    logger.error(f"Lỗi API ({response.status}): {error_content}")
                    if response.status in retryable_codes:
                        sleep_time = (2 ** attempt) + random.random()
                        logger.warning(f"⚠️ Lỗi {response.status}, đợi {sleep_time:.2f}s, lần thử {attempt+1}/{max_retries}")
                        time.sleep(sleep_time)
                        continue
                    else:
                        return None

        except urllib.error.HTTPError as e:
            if e.code == 451:
                logger.error("❌ Lỗi 451: Truy cập bị chặn - Kiểm tra VPN/proxy")
                return None
            else:
                logger.error(f"Lỗi HTTP ({e.code}): {e.reason}")

            if e.code in retryable_codes:
                sleep_time = (2 ** attempt) + random.random()
                logger.warning(f"⚠️ HTTP {e.code}, đợi {sleep_time:.2f}s, lần thử {attempt+1}/{max_retries}")
                time.sleep(sleep_time)
                continue
            else:
                return None

        except Exception as e:
            error_name = type(e).__name__
            if any(ret in error_name for ret in retryable_errors) or 'timeout' in str(e).lower():
                sleep_time = (2 ** attempt) + random.random()
                logger.warning(f"⚠️ Lỗi kết nối ({error_name}), đợi {sleep_time:.2f}s, lần thử {attempt+1}/{max_retries}: {str(e)}")
                time.sleep(sleep_time)
                continue
            else:
                logger.error(f"Lỗi không xác định (lần thử {attempt + 1}): {str(e)}")
                if attempt == max_retries - 1:
                    return None
                time.sleep(0.5)

    logger.error(f"❌ Thất bại yêu cầu API sau {max_retries} lần thử: {base_url}")
    return None

# ========== HÀM CACHE COIN ==========
def refresh_coins_cache():
    try:
        url = "https://fapi.binance.com/fapi/v1/exchangeInfo"
        data = binance_api_request(url)
        if not data:
            logger.error("❌ Không thể lấy exchangeInfo từ Binance")
            return False

        coins = []
        for symbol_info in data.get('symbols', []):
            symbol = symbol_info.get('symbol', '')
            quote = symbol_info.get('quoteAsset', '')
            if quote not in ('USDT', 'USDC'):
                continue
            if symbol_info.get('status') != 'TRADING':
                continue
            if symbol in _SYMBOL_BLACKLIST:
                continue

            max_leverage = 50
            for f in symbol_info.get('filters', []):
                if f['filterType'] == 'LEVERAGE' and 'maxLeverage' in f:
                    max_leverage = int(f['maxLeverage'])
                    break

            step_size = 0.001
            min_qty = 0.001
            min_notional = 5.0
            for f in symbol_info.get('filters', []):
                if f['filterType'] == 'LOT_SIZE':
                    step_size = float(f['stepSize'])
                    min_qty = float(f.get('minQty', step_size))
                if f['filterType'] == 'MIN_NOTIONAL':
                    min_notional = float(f.get('notional', 5.0))

            coins.append({
                'symbol': symbol,
                'quote': quote,
                'max_leverage': max_leverage,
                'step_size': step_size,
                'min_qty': min_qty,
                'min_notional': min_notional,
                'price': 0.0,
                'volume': 0.0,
                'last_price_update': 0,
                'last_volume_update': 0
            })

        _COINS_CACHE.update_data(coins)
        _COINS_CACHE.update_volume_time()
        logger.info(f"✅ Đã cập nhật cache {len(coins)} coin USDT/USDC")
        return True

    except Exception as e:
        logger.error(f"❌ Lỗi refresh cache coin: {str(e)}")
        logger.error(traceback.format_exc())
        return False

def update_coins_price():
    try:
        url = "https://fapi.binance.com/fapi/v1/ticker/price"
        all_prices = binance_api_request(url)
        if not all_prices:
            return False

        price_dict = {item['symbol']: float(item['price']) for item in all_prices}
        coins = _COINS_CACHE.get_data()
        updated = 0
        for coin in coins:
            if coin['symbol'] in price_dict:
                coin['price'] = price_dict[coin['symbol']]
                coin['last_price_update'] = time.time()
                updated += 1
        _COINS_CACHE.update_data(coins)
        _COINS_CACHE.update_price_time()
        logger.info(f"✅ Đã cập nhật giá cho {updated} coin")
        return True
    except Exception as e:
        logger.error(f"❌ Lỗi cập nhật giá: {str(e)}")
        return False

def update_coins_volume():
    try:
        url = "https://fapi.binance.com/fapi/v1/ticker/24hr"
        all_tickers = binance_api_request(url)
        if not all_tickers:
            return False

        volume_dict = {item['symbol']: float(item['volume']) for item in all_tickers}
        coins = _COINS_CACHE.get_data()
        updated = 0
        for coin in coins:
            if coin['symbol'] in volume_dict:
                coin['volume'] = volume_dict[coin['symbol']]
                coin['last_volume_update'] = time.time()
                updated += 1
        _COINS_CACHE.update_data(coins)
        _COINS_CACHE.update_volume_time()
        logger.info(f"✅ Đã cập nhật volume cho {updated} coin")
        return True
    except Exception as e:
        logger.error(f"❌ Lỗi cập nhật volume: {str(e)}")
        return False

def get_coins_with_info():
    return _COINS_CACHE.get_data()

def get_max_leverage_from_cache(symbol):
    symbol = symbol.upper()
    coins = _COINS_CACHE.get_data()
    for coin in coins:
        if coin['symbol'] == symbol:
            return coin['max_leverage']
    logger.warning(f"⚠️ Không tìm thấy {symbol} trong cache, dùng mặc định 50x")
    return 50

def get_min_notional_from_cache(symbol):
    symbol = symbol.upper()
    coins = _COINS_CACHE.get_data()
    for coin in coins:
        if coin['symbol'] == symbol:
            return coin.get('min_notional', 5.0)
    return 5.0

def get_min_qty_from_cache(symbol):
    symbol = symbol.upper()
    coins = _COINS_CACHE.get_data()
    for coin in coins:
        if coin['symbol'] == symbol:
            return coin.get('min_qty', 0.001)
    return 0.001

def get_step_size(symbol):
    if not symbol: return 0.001
    coins = _COINS_CACHE.get_data()
    for coin in coins:
        if coin['symbol'] == symbol.upper():
            return coin['step_size']
    return 0.001

def force_refresh_coin_cache():
    logger.info("🔄 Buộc làm mới cache coin...")
    if refresh_coins_cache():
        update_coins_volume()
        update_coins_price()
        return True
    return False

# ========== HÀM LỌC COIN ==========
def filter_coins_for_side(side, excluded_coins=None):
    all_coins = get_coins_with_info()
    filtered = []

    if not all_coins:
        logger.warning("❌ Cache coin trống!")
        return filtered

    max_price_buy = _BALANCE_CONFIG.get("max_price_buy", float('inf'))
    max_volume_buy = _BALANCE_CONFIG.get("max_volume_buy", float('inf'))
    min_price_sell = _BALANCE_CONFIG.get("min_price_sell", 0.0)
    min_volume_sell = _BALANCE_CONFIG.get("min_volume_sell", 0.0)

    logger.info(f"🔍 Lọc coin cho hướng {side} | Tổng số coin: {len(all_coins)}")
    if side == "BUY":
        logger.info(f"⚙️ Điều kiện MUA: giá ≤ {max_price_buy} USDT, volume ≤ {max_volume_buy}")
    else:
        logger.info(f"⚙️ Điều kiện BÁN: giá ≥ {min_price_sell} USDT, volume ≥ {min_volume_sell}")

    excluded_set = set(excluded_coins or [])
    blacklisted = 0
    excluded_cnt = 0
    condition_fail = 0
    volume_zero = 0
    price_zero = 0

    for coin in all_coins:
        sym = coin['symbol']
        if sym in _SYMBOL_BLACKLIST:
            blacklisted += 1
            continue
        if sym in excluded_set:
            excluded_cnt += 1
            continue
        if coin['price'] <= 0:
            price_zero += 1
            continue
        if coin['volume'] <= 0:
            volume_zero += 1

        if side == "BUY":
            if coin['price'] > max_price_buy and coin['volume'] > max_volume_buy:
                condition_fail += 1
                continue
        else:  # SELL
            if coin['price'] < min_price_sell and coin['volume'] < min_volume_sell:
                condition_fail += 1
                continue

        filtered.append(coin)

    logger.info(f"📊 {side}: {len(filtered)} coin phù hợp (loại: blacklist={blacklisted}, excluded={excluded_cnt}, không thỏa điều kiện={condition_fail}, volume0={volume_zero}, price0={price_zero})")
    if filtered:
        for i, c in enumerate(filtered[:5]):
            logger.info(f"  {i+1}. {c['symbol']} | giá: {c['price']:.4f} | volume: {c['volume']:.2f}")

    return filtered

def update_balance_config(max_price_buy=None, max_volume_buy=None, min_price_sell=None, min_volume_sell=None,
                          min_leverage=None, sort_by_volume=None):
    _BALANCE_CONFIG.update(
        max_price_buy=max_price_buy,
        max_volume_buy=max_volume_buy,
        min_price_sell=min_price_sell,
        min_volume_sell=min_volume_sell,
        min_leverage=min_leverage,
        sort_by_volume=sort_by_volume
    )
    logger.info(f"✅ Cập nhật cấu hình lọc: {_BALANCE_CONFIG.get_all()}")
    return _BALANCE_CONFIG.get_all()

# ========== CÁC HÀM API BINANCE KHÁC ==========
def set_leverage(symbol, lev, api_key, api_secret):
    if not symbol: return False
    try:
        ts = int(time.time() * 1000)
        params = {"symbol": symbol.upper(), "leverage": lev, "timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v1/leverage?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        response = binance_api_request(url, method='POST', headers=headers)
        return bool(response and 'leverage' in response)
    except Exception as e:
        logger.error(f"Lỗi cài đặt đòn bẩy: {str(e)}")
        return False

def get_balance(api_key, api_secret):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/account?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        data = binance_api_request(url, headers=headers)
        if not data: return None
        for asset in data['assets']:
            if asset['asset'] in ('USDT', 'USDC'):
                available_balance = float(asset['availableBalance'])
                logger.info(f"💰 Số dư - Khả dụng: {available_balance:.2f} {asset['asset']}")
                return available_balance
        return 0
    except Exception as e:
        logger.error(f"Lỗi số dư: {str(e)}")
        return None

def get_total_and_available_balance(api_key, api_secret):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/account?{query}&signature={sig}"
        headers = {"X-MBX-APIKEY": api_key}
        data = binance_api_request(url, headers=headers)
        if not data:
            logger.error("❌ Không lấy được số dư từ Binance")
            return None, None
        total_all = 0.0
        available_all = 0.0
        for asset in data["assets"]:
            if asset["asset"] in ("USDT", "USDC"):
                available_all += float(asset["availableBalance"])
                total_all += float(asset["walletBalance"])
        logger.info(f"💰 Tổng số dư (USDT+USDC): {total_all:.2f}, Khả dụng: {available_all:.2f}")
        return total_all, available_all
    except Exception as e:
        logger.error(f"Lỗi lấy tổng số dư: {str(e)}")
        return None, None

def get_margin_balance(api_key, api_secret):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/account?{query}&signature={sig}"
        headers = {"X-MBX-APIKEY": api_key}
        data = binance_api_request(url, headers=headers)
        if not data:
            return None
        margin_balance = float(data.get("totalMarginBalance", 0.0))
        logger.info(f"💰 Số dư ký quỹ: {margin_balance:.2f}")
        return margin_balance
    except Exception as e:
        logger.error(f"Lỗi lấy số dư ký quỹ: {str(e)}")
        return None

def get_margin_safety_info(api_key, api_secret):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/account?{query}&signature={sig}"
        headers = {"X-MBX-APIKEY": api_key}
        data = binance_api_request(url, headers=headers)
        if not data:
            logger.error("❌ Không lấy được thông tin ký quỹ từ Binance")
            return None, None, None
        margin_balance = float(data.get("totalMarginBalance", 0.0))
        maint_margin = float(data.get("totalMaintMargin", 0.0))
        if maint_margin <= 0:
            logger.warning(f"⚠️ Maint margin <= 0 (margin_balance={margin_balance:.4f}, maint_margin={maint_margin:.4f})")
            return margin_balance, maint_margin, None
        ratio = margin_balance / maint_margin
        logger.info(f"🛡️ An toàn ký quỹ: margin_balance={margin_balance:.4f}, maint_margin={maint_margin:.4f}, tỷ lệ={ratio:.2f}x")
        return margin_balance, maint_margin, ratio
    except Exception as e:
        logger.error(f"Lỗi lấy thông tin an toàn ký quỹ: {str(e)}")
        return None, None, None

def place_order(symbol, side, qty, api_key, api_secret):
    if not symbol: return None
    try:
        ts = int(time.time() * 1000)
        params = {
            "symbol": symbol.upper(),
            "side": side,
            "type": "MARKET",
            "quantity": qty,
            "timestamp": ts
        }
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v1/order?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        return binance_api_request(url, method='POST', headers=headers)
    except Exception as e:
        logger.error(f"Lỗi lệnh: {str(e)}")
        return None

def cancel_all_orders(symbol, api_key, api_secret):
    if not symbol: return False
    try:
        ts = int(time.time() * 1000)
        params = {"symbol": symbol.upper(), "timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v1/allOpenOrders?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        response = binance_api_request(url, method='DELETE', headers=headers)
        return response is not None
    except Exception as e:
        logger.error(f"Lỗi hủy lệnh: {str(e)}")
        return False

def get_current_price(symbol):
    if not symbol: return 0
    try:
        url = f"https://fapi.binance.com/fapi/v1/ticker/price?symbol={symbol.upper()}"
        data = binance_api_request(url)
        if data and 'price' in data:
            price = float(data['price'])
            return price if price > 0 else 0
        return 0
    except Exception as e:
        logger.error(f"Lỗi giá {symbol}: {str(e)}")
        return 0

# ========== CACHE MARK PRICE (TTL 1 giây) ==========
_mark_price_cache = {}
_mark_price_time = {}

def get_mark_price(symbol):
    if not symbol:
        return 0
    now = time.time()
    if symbol in _mark_price_cache and (now - _mark_price_time.get(symbol, 0)) < 1.0:
        return _mark_price_cache[symbol]
    try:
        url = f"https://fapi.binance.com/fapi/v1/premiumIndex?symbol={symbol.upper()}"
        data = binance_api_request(url)
        if data and 'markPrice' in data:
            price = float(data['markPrice'])
            _mark_price_cache[symbol] = price
            _mark_price_time[symbol] = now
            return price
    except Exception as e:
        logger.error(f"Lỗi lấy mark price {symbol}: {e}")
    price = get_current_price(symbol)
    _mark_price_cache[symbol] = price
    _mark_price_time[symbol] = now
    return price

# ========== HÀM PHÂN TÍCH TÍN HIỆU DỰA TRÊN 2 NẾN 15 PHÚT ==========
def get_candle_signal_15m(symbol):
    """
    Phân tích 2 nến 15 phút gần nhất:
    - Nếu vol_prev > vol_curr: tín hiệu NGƯỢC hướng với nến hiện tại
      (nến green -> SELL, nến red -> BUY)
    - Nếu vol_prev <= vol_curr: tín hiệu CÙNG hướng với nến hiện tại
      (nến green -> BUY, nến red -> SELL)
    Trả về 'BUY', 'SELL' hoặc None nếu không đủ dữ liệu.
    """
    try:
        url = "https://fapi.binance.com/fapi/v1/klines"
        params = {"symbol": symbol.upper(), "interval": "15m", "limit": 2}
        data = binance_api_request(url, params=params)
        if not data or len(data) < 2:
            return None
        prev = data[0]
        curr = data[1]
        vol_prev = float(prev[5])
        vol_curr = float(curr[5])
        open_curr = float(curr[1])
        close_curr = float(curr[4])
        is_green = close_curr > open_curr

        if vol_prev > vol_curr:
            # Ngược hướng với nến hiện tại
            return "SELL" if is_green else "BUY"
        else:  # vol_prev <= vol_curr
            # Cùng hướng với nến hiện tại
            return "BUY" if is_green else "SELL"
    except Exception as e:
        logger.error(f"Lỗi phân tích tín hiệu nến 15m {symbol}: {e}")
        return None

# ========== HÀM KIỂM TRA VỊ THẾ ==========
def get_positions(symbol=None, api_key=None, api_secret=None):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        if symbol: params["symbol"] = symbol.upper()
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/positionRisk?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        positions = binance_api_request(url, headers=headers)
        if not positions: return []
        if symbol:
            for pos in positions:
                if pos['symbol'] == symbol.upper():
                    return [pos]
        return positions
    except Exception as e:
        logger.error(f"Lỗi vị thế: {str(e)}")
        return []

def has_open_position(symbol, api_key, api_secret):
    positions = get_positions(symbol, api_key, api_secret)
    for pos in positions:
        if abs(float(pos.get('positionAmt', 0))) > 0:
            return True
    return False

# ========== LỚP QUẢN LÝ ==========
class CoinManager:
    def __init__(self):
        self.active_coins = set()
        self._lock = threading.RLock()

    def register_coin(self, symbol):
        if not symbol: return
        with self._lock: self.active_coins.add(symbol.upper())

    def unregister_coin(self, symbol):
        if not symbol: return
        with self._lock: self.active_coins.discard(symbol.upper())

    def is_coin_active(self, symbol):
        if not symbol: return False
        with self._lock: return symbol.upper() in self.active_coins

    def get_active_coins(self):
        with self._lock: return list(self.active_coins)

class BotExecutionCoordinator:
    def __init__(self):
        self._lock = threading.RLock()
        self._bot_queue = queue.Queue()
        self._current_finding_bot = None
        self._found_coins = set()
        self._bots_with_coins = set()
        self._temp_blacklist = {}
        self._blacklist_lock = threading.RLock()

    def add_temp_blacklist(self, symbol, duration=300):
        expiry = time.time() + duration
        with self._blacklist_lock:
            self._temp_blacklist[symbol.upper()] = expiry
        logger.info(f"⏳ Blacklist tạm: {symbol} trong {duration}s")

    def is_temp_blacklisted(self, symbol):
        symbol = symbol.upper()
        now = time.time()
        with self._blacklist_lock:
            expired = [s for s, exp in self._temp_blacklist.items() if exp <= now]
            for s in expired:
                del self._temp_blacklist[s]
            return symbol in self._temp_blacklist

    def release_coin(self, symbol):
        with self._lock:
            self._found_coins.discard(symbol.upper())

    def request_coin_search(self, bot_id):
        with self._lock:
            if bot_id in self._bots_with_coins:
                return False
            if self._current_finding_bot is None or self._current_finding_bot == bot_id:
                self._current_finding_bot = bot_id
                return True
            else:
                if bot_id not in list(self._bot_queue.queue):
                    self._bot_queue.put(bot_id)
                return False

    def finish_coin_search(self, bot_id, found_symbol=None, has_coin_now=False):
        next_bot = None
        with self._lock:
            if self._current_finding_bot == bot_id:
                self._current_finding_bot = None
                if found_symbol:
                    self._found_coins.add(found_symbol)
                if has_coin_now:
                    self._bots_with_coins.add(bot_id)
                if not self._bot_queue.empty():
                    try:
                        next_bot = self._bot_queue.get_nowait()
                        self._current_finding_bot = next_bot
                    except queue.Empty:
                        pass
        return next_bot

    def bot_has_coin(self, bot_id):
        with self._lock:
            self._bots_with_coins.add(bot_id)
            new_queue = queue.Queue()
            while not self._bot_queue.empty():
                try:
                    b = self._bot_queue.get_nowait()
                    if b != bot_id:
                        new_queue.put(b)
                except queue.Empty:
                    break
            self._bot_queue = new_queue

    def bot_lost_coin(self, bot_id):
        with self._lock:
            self._bots_with_coins.discard(bot_id)

    def remove_bot(self, bot_id):
        with self._lock:
            if self._current_finding_bot == bot_id:
                self._current_finding_bot = None
            self._bots_with_coins.discard(bot_id)
            new_queue = queue.Queue()
            while not self._bot_queue.empty():
                try:
                    b = self._bot_queue.get_nowait()
                    if b != bot_id:
                        new_queue.put(b)
                except queue.Empty:
                    break
            self._bot_queue = new_queue

    def get_queue_info(self):
        with self._lock:
            return {
                'current_finding': self._current_finding_bot,
                'queue_size': self._bot_queue.qsize(),
                'queue_bots': list(self._bot_queue.queue),
                'bots_with_coins': list(self._bots_with_coins),
                'found_coins_count': len(self._found_coins)
            }

    def get_queue_position(self, bot_id):
        with self._lock:
            if self._current_finding_bot == bot_id:
                return 0
            else:
                queue_list = list(self._bot_queue.queue)
                return queue_list.index(bot_id) + 1 if bot_id in queue_list else -1

class SmartCoinFinder:
    def __init__(self, api_key, api_secret):
        self.api_key = api_key
        self.api_secret = api_secret
        self.last_scan_time = 0
        self.scan_cooldown = 30
        self.position_counts = {"BUY": 0, "SELL": 0}
        self.last_position_count_update = 0
        self._bot_manager = None
        self.bot_leverage = 10

    def set_bot_manager(self, bot_manager):
        self._bot_manager = bot_manager

    def find_best_coin_with_balance(self, excluded_coins=None):
        try:
            now = time.time()
            if now - self.last_scan_time < self.scan_cooldown:
                return None
            self.last_scan_time = now

            coins = get_coins_with_info()
            if not coins:
                logger.warning("⚠️ Cache coin trống, không thể tìm coin.")
                return None

            if self._bot_manager and hasattr(self._bot_manager, 'global_side_coordinator'):
                global_side = self._bot_manager.global_side_coordinator.get_next_side(
                    self.api_key, self.api_secret
                )
            else:
                global_side = random.choice(["BUY", "SELL"])

            logger.info(f"🎯 Hệ thống chọn hướng: {global_side} (đòn bẩy bot: {self.bot_leverage}x)")

            filtered_coins = filter_coins_for_side(global_side, excluded_coins)

            if not filtered_coins:
                return None

            for coin in filtered_coins:
                symbol = coin['symbol']
                if self._bot_manager and self._bot_manager.bot_coordinator.is_temp_blacklisted(symbol):
                    continue
                if has_open_position(symbol, self.api_key, self.api_secret):
                    continue
                if self._bot_manager and self._bot_manager.coin_manager.is_coin_active(symbol):
                    continue

                # Kiểm tra tín hiệu nến 15 phút
                local_signal = get_candle_signal_15m(symbol)
                if local_signal is None or local_signal != global_side:
                    continue

                logger.info(f"✅ Tìm thấy coin {symbol} phù hợp ({global_side}) | volume: {coin['volume']:.2f}")
                return symbol

            return None

        except Exception as e:
            logger.error(f"❌ Lỗi tìm coin với cân bằng: {str(e)}")
            logger.error(traceback.format_exc())
            return None

# ========== WEBSOCKET MANAGER ==========
class WebSocketManager:
    def __init__(self):
        self.connections = {}
        self.executor = ThreadPoolExecutor(max_workers=20, thread_name_prefix='ws_executor')
        self._lock = threading.RLock()
        self._stop_event = threading.Event()
        self.price_cache = {}
        self.last_price_update = {}

    def add_symbol(self, symbol, callback):
        if not symbol: return
        symbol = symbol.upper()
        with self._lock:
            if symbol not in self.connections:
                self._create_connection(symbol, callback)

    def _create_connection(self, symbol, callback):
        if self._stop_event.is_set(): return
        streams = [f"{symbol.lower()}@trade"]
        url = f"wss://fstream.binance.com/stream?streams={'/'.join(streams)}"

        def on_message(ws, message):
            try:
                data = json.loads(message)
                if 'data' in data:
                    sym = data['data']['s']
                    price = float(data['data']['p'])
                    current_time = time.time()
                    if (sym in self.last_price_update and
                        current_time - self.last_price_update[sym] < 0.1):
                        return
                    self.last_price_update[sym] = current_time
                    self.price_cache[sym] = price
                    self.executor.submit(callback, price)
            except Exception as e:
                logger.error(f"Lỗi tin nhắn WebSocket {symbol}: {str(e)}")

        def on_error(ws, error):
            logger.error(f"Lỗi WebSocket {symbol}: {str(error)}")
            if not self._stop_event.is_set():
                time.sleep(5)
                self._reconnect(symbol, callback)

        def on_close(ws, close_status_code, close_msg):
            logger.info(f"WebSocket đã đóng {symbol}: {close_status_code} - {close_msg}")
            if not self._stop_event.is_set() and symbol in self.connections:
                time.sleep(5)
                self._reconnect(symbol, callback)

        ws = websocket.WebSocketApp(url, on_message=on_message, on_error=on_error, on_close=on_close)
        thread = threading.Thread(target=ws.run_forever, daemon=True, name=f"ws-{symbol}")
        thread.start()
        self.connections[symbol] = {'ws': ws, 'thread': thread, 'callback': callback}
        logger.info(f"🔗 WebSocket đã khởi động cho {symbol}")

    def _reconnect(self, symbol, callback):
        logger.info(f"Đang kết nối lại WebSocket cho {symbol}")
        self.remove_symbol(symbol)
        self._create_connection(symbol, callback)

    def remove_symbol(self, symbol):
        if not symbol: return
        symbol = symbol.upper()
        with self._lock:
            if symbol in self.connections:
                try:
                    self.connections[symbol]['ws'].close()
                except Exception as e:
                    logger.error(f"Lỗi đóng WebSocket {symbol}: {str(e)}")
                self.connections[symbol]['callback'] = None
                del self.connections[symbol]
                self.price_cache.pop(symbol, None)
                self.last_price_update.pop(symbol, None)
                logger.info(f"WebSocket đã xóa cho {symbol}")

    def stop(self):
        self._stop_event.set()
        for symbol in list(self.connections.keys()):
            self.remove_symbol(symbol)
        self.executor.shutdown(wait=False)

# ========== LỚP BaseBot (CHỈ DÙNG TÍN HIỆU 15M, KHÔNG TP/SL, KHÔNG PYRAMIDING) ==========
class BaseBot:
    def __init__(self, symbol, lev, percent, ws_manager, api_key, api_secret,
                 telegram_bot_token, telegram_chat_id, strategy_name, config_key=None, bot_id=None,
                 coin_manager=None, symbol_locks=None, max_coins=1, bot_coordinator=None,
                 enable_balance_orders=True, **kwargs):

        self.max_coins = 1
        self.active_symbols = []
        self.symbol_data = {}
        self.symbol = symbol.upper() if symbol else None

        self.lev = lev
        self.percent = percent
        self.ws_manager = ws_manager
        self.api_key = api_key
        self.api_secret = api_secret
        self.telegram_bot_token = telegram_bot_token
        self.telegram_chat_id = telegram_chat_id
        self.strategy_name = strategy_name
        self.config_key = config_key
        self.bot_id = bot_id or f"{strategy_name}_{int(time.time())}_{random.randint(1000, 9999)}"

        # Tắt hết các tính năng cũ
        self.tp = None
        self.sl = None
        self.roi_trigger = None
        self.pyramiding_enabled = False

        self.status = "searching" if not symbol else "waiting"
        self._stop = False

        self.current_processing_symbol = None
        self.last_trade_completion_time = 0
        self.trade_cooldown = 30

        self.last_global_position_check = 0
        self.last_error_log_time = 0
        self.global_position_check_interval = 30

        self.global_long_count = 0
        self.global_short_count = 0
        self.global_long_pnl = 0
        self.global_short_pnl = 0
        self.global_long_volume = 0.0
        self.global_short_volume = 0.0
        self.next_global_side = None

        self.margin_safety_threshold = 1.05
        self.margin_safety_interval = 10
        self.last_margin_safety_check = 0

        self.coin_manager = coin_manager or CoinManager()
        self.symbol_locks = symbol_locks or defaultdict(threading.RLock)
        self.coin_finder = SmartCoinFinder(api_key, api_secret)
        self.coin_finder.bot_leverage = self.lev

        self.find_new_bot_after_close = True
        self.bot_creation_time = time.time()

        self.execution_lock = threading.RLock()
        self.last_execution_time = 0
        self.execution_cooldown = 1

        self.bot_coordinator = bot_coordinator or BotExecutionCoordinator()

        self.enable_balance_orders = enable_balance_orders
        self.balance_config = {
            'max_price_buy': kwargs.get('max_price_buy', float('inf')),
            'max_volume_buy': kwargs.get('max_volume_buy', float('inf')),
            'min_price_sell': kwargs.get('min_price_sell', 0.0),
            'min_volume_sell': kwargs.get('min_volume_sell', 0.0),
            'min_leverage': _BALANCE_CONFIG.get("min_leverage", 10)
        }
        update_balance_config(
            max_price_buy=self.balance_config['max_price_buy'],
            max_volume_buy=self.balance_config['max_volume_buy'],
            min_price_sell=self.balance_config['min_price_sell'],
            min_volume_sell=self.balance_config['min_volume_sell']
        )

        self.consecutive_failures = 0
        self.failure_cooldown_until = 0

        # Theo dõi nến 15 phút đã xử lý
        self.last_candle_check = {}   # symbol -> last_close_time

        if symbol and not has_open_position(symbol, self.api_key, self.api_secret):
            self._add_symbol(symbol)

        self.thread = threading.Thread(target=self._run, daemon=True, name=f"bot-{self.bot_id[-8:]}")
        self.thread.start()

        self.log(f"🟢 Bot {strategy_name} đã khởi động | 1 coin | Đòn bẩy: {lev}x | Vốn: {percent}% | Tín hiệu: 2 nến 15m | Không TP/SL")

    def _run(self):
        last_coin_search_log = 0
        log_interval = 30
        last_no_coin_found_log = 0

        while not self._stop:
            try:
                current_time = time.time()

                if current_time < self.failure_cooldown_until:
                    time.sleep(1)
                    continue

                if current_time - self.last_margin_safety_check > self.margin_safety_interval:
                    self.last_margin_safety_check = current_time
                    if self._check_margin_safety():
                        time.sleep(5)
                        continue

                if current_time - self.last_global_position_check > 30:
                    self.check_global_positions()
                    self.last_global_position_check = current_time

                if not self.active_symbols:
                    search_permission = self.bot_coordinator.request_coin_search(self.bot_id)

                    if search_permission:
                        if current_time - last_coin_search_log > log_interval:
                            queue_info = self.bot_coordinator.get_queue_info()
                            self.log(f"🔍 Đang tìm coin (vị trí: 1/{queue_info['queue_size'] + 1})...")
                            last_coin_search_log = current_time

                        found_coin = None
                        if self.enable_balance_orders:
                            found_coin = self.coin_finder.find_best_coin_with_balance(
                                excluded_coins=self.coin_manager.get_active_coins()
                            )

                        if found_coin:
                            self.bot_coordinator.bot_has_coin(self.bot_id)
                            self._add_symbol(found_coin)
                            self.bot_coordinator.finish_coin_search(self.bot_id, found_coin, has_coin_now=True)
                            self.log(f"✅ Đã tìm thấy coin: {found_coin}, đang chờ vào lệnh...")
                            last_coin_search_log = 0
                        else:
                            self.bot_coordinator.finish_coin_search(self.bot_id)
                            if current_time - last_no_coin_found_log > 60:
                                self.log(f"❌ Không tìm thấy coin phù hợp")
                                last_no_coin_found_log = current_time
                    else:
                        queue_pos = self.bot_coordinator.get_queue_position(self.bot_id)
                        if queue_pos > 0:
                            if current_time - last_coin_search_log > log_interval:
                                last_coin_search_log = current_time
                        time.sleep(2)

                    time.sleep(5)
                    continue

                for symbol in self.active_symbols.copy():
                    position_opened = self._process_single_symbol(symbol)
                    if position_opened:
                        self.log(f"🎯 Đã vào lệnh thành công {symbol}, chuyển quyền tìm coin...")
                        next_bot = self.bot_coordinator.finish_coin_search(self.bot_id)
                        if next_bot:
                            self.log(f"🔄 Đã chuyển quyền tìm coin cho bot: {next_bot}")
                        break

                time.sleep(1)

            except Exception as e:
                if time.time() - self.last_error_log_time > 10:
                    self.log(f"❌ Lỗi hệ thống: {str(e)}")
                    self.last_error_log_time = time.time()
                time.sleep(5)

    def _process_single_symbol(self, symbol):
        try:
            if symbol not in self.symbol_data:
                return False
            symbol_info = self.symbol_data[symbol]
            current_time = time.time()

            # Timeout 5 phút nếu chưa vào được lệnh
            if not symbol_info['position_open'] and current_time - symbol_info.get('added_time', current_time) > 300:
                self.log(f"⏰ {symbol} đã chờ vào lệnh quá 5 phút, dừng để tìm coin khác")
                self.stop_symbol(symbol, failed=True)
                return False

            if current_time - symbol_info.get('last_position_check', 0) > 30:
                self._check_symbol_position(symbol)
                symbol_info['last_position_check'] = current_time

            if symbol_info['position_open']:
                # Chỉ kiểm tra thoát lệnh theo nến 15 phút
                self._check_candle_exit_15m(symbol)
                return False
            else:
                if (current_time - symbol_info['last_trade_time'] > 30 and
                    current_time - symbol_info['last_close_time'] > 30):

                    target_side = self.get_next_side_based_on_comprehensive_analysis()
                    logger.info(f"🎯 Hướng giao dịch cho {symbol}: {target_side}")

                    if not has_open_position(symbol, self.api_key, self.api_secret):
                        try:
                            if self._open_symbol_position(symbol, target_side):
                                symbol_info['last_trade_time'] = current_time
                                return True
                        except Exception as e:
                            self.log(f"❌ Lỗi nghiêm trọng khi mở lệnh {symbol}: {str(e)}")
                            self.stop_symbol(symbol, failed=True)
                            return False
                return False
        except Exception as e:
            self.log(f"❌ Lỗi xử lý {symbol}: {str(e)}")
            return False

    def _add_symbol(self, symbol):
        symbol = symbol.upper()
        if symbol in self.active_symbols:
            return
        self.active_symbols.append(symbol)
        self.symbol_data[symbol] = {
            'position_open': False,
            'entry': 0,
            'entry_base': 0,
            'side': None,
            'qty': 0,
            'status': 'waiting',
            'last_price': 0,
            'last_price_time': 0,
            'last_trade_time': 0,
            'last_close_time': 0,
            'last_position_check': 0,
            'failed_attempts': 0,
            'added_time': time.time()
        }
        self.ws_manager.add_symbol(symbol, lambda p, s=symbol: self._handle_price_update(s, p))
        self.coin_manager.register_coin(symbol)
        self.log(f"➕ Đã thêm {symbol} vào theo dõi")

    def _handle_price_update(self, symbol, price):
        if symbol not in self.symbol_data:
            return
        self.symbol_data[symbol]['last_price'] = price
        self.symbol_data[symbol]['last_price_time'] = time.time()

    def get_current_price(self, symbol):
        if symbol in self.symbol_data and self.symbol_data[symbol]['last_price'] > 0:
            return self.symbol_data[symbol]['last_price']
        return get_current_price(symbol)

    def _get_fresh_price(self, symbol):
        data = self.symbol_data.get(symbol)
        if data and time.time() - data.get('last_price_time', 0) < 5:
            return data['last_price']
        price = get_current_price(symbol)
        if price > 0 and data:
            data['last_price'] = price
            data['last_price_time'] = time.time()
        return price

    def _force_check_position(self, symbol):
        try:
            positions = get_positions(symbol, self.api_key, self.api_secret)
            if positions and len(positions) > 0:
                pos = positions[0]
                amt = float(pos.get('positionAmt', 0))
                if abs(amt) > 0:
                    return pos
            return None
        except Exception as e:
            logger.error(f"Lỗi force check position {symbol}: {str(e)}")
            return None

    def _check_symbol_position(self, symbol):
        try:
            positions = get_positions(symbol, self.api_key, self.api_secret)
            if not positions or len(positions) == 0:
                time.sleep(2)
                positions = get_positions(symbol, self.api_key, self.api_secret)
            if positions and len(positions) > 0:
                pos = positions[0]
                amt = float(pos.get('positionAmt', 0))
                if abs(amt) > 0:
                    if not self.symbol_data[symbol]['position_open']:
                        entry_price = float(pos.get('entryPrice', 0))
                        if entry_price == 0:
                            self.log(f"⚠️ {symbol} - entryPrice = 0, bỏ qua cập nhật")
                            return
                        self.symbol_data[symbol].update({
                            'position_open': True,
                            'entry': entry_price,
                            'entry_base': entry_price,
                            'qty': amt,
                            'side': 'BUY' if amt > 0 else 'SELL',
                            'status': 'open'
                        })
                        self.log(f"📌 Phát hiện vị thế {symbol} từ API")
                else:
                    if self.symbol_data[symbol]['position_open']:
                        self._reset_symbol_position(symbol)
            else:
                if self.symbol_data[symbol]['position_open']:
                    self._reset_symbol_position(symbol)
        except Exception as e:
            logger.error(f"Lỗi kiểm tra vị thế {symbol}: {str(e)}")

    def _reset_symbol_position(self, symbol):
        if symbol in self.symbol_data:
            self.symbol_data[symbol].update({
                'position_open': False,
                'entry': 0,
                'entry_base': 0,
                'side': None,
                'qty': 0,
                'status': 'closed',
            })
            self.symbol_data[symbol]['last_close_time'] = time.time()
            # Xóa theo dõi nến khi đóng lệnh
            self.last_candle_check.pop(symbol, None)

    # ---------- MỞ LỆNH ----------
    def _open_symbol_position(self, symbol, side):
        with self.symbol_locks[symbol]:
            try:
                if has_open_position(symbol, self.api_key, self.api_secret):
                    self.log(f"⚠️ {symbol} đã có vị thế, không mở thêm")
                    self.stop_symbol(symbol, failed=True)
                    return False

                # Kiểm tra tín hiệu nến 15 phút ngay trước khi vào lệnh
                local_signal = get_candle_signal_15m(symbol)
                if local_signal is None or local_signal != side:
                    self.log(f"⚠️ {symbol} tín hiệu nến không còn phù hợp ({local_signal} vs {side})")
                    if hasattr(self, '_bot_manager') and self._bot_manager:
                        self._bot_manager.bot_coordinator.add_temp_blacklist(symbol, duration=60)
                    self.stop_symbol(symbol, failed=True)
                    return False

                if not set_leverage(symbol, self.lev, self.api_key, self.api_secret):
                    self.log(f"❌ {symbol} - Không thể cài đặt đòn bẩy {self.lev}x")
                    self.stop_symbol(symbol, failed=True)
                    return False

                total_balance, available_balance = get_total_and_available_balance(self.api_key, self.api_secret)
                if total_balance is None or total_balance <= 0:
                    self.log(f"❌ {symbol} - Không thể lấy tổng số dư")
                    self.stop_symbol(symbol, failed=True)
                    return False

                required_usd = total_balance * (self.percent / 100)
                if required_usd <= 0:
                    self.log(f"❌ {symbol} - Tổng số dư quá nhỏ ({total_balance:.2f})")
                    self.stop_symbol(symbol, failed=True)
                    return False

                if required_usd > available_balance:
                    self.log(f"⚠️ {symbol} - {self.percent}% tổng số dư ({required_usd:.2f}) > số dư khả dụng ({available_balance:.2f}), vẫn thử lệnh...")

                current_price = self._get_fresh_price(symbol)
                if current_price <= 0:
                    self.log(f"❌ {symbol} - Lỗi giá")
                    self.stop_symbol(symbol, failed=True)
                    return False

                # Kiểm tra điều kiện cân bằng nếu bật
                if self.enable_balance_orders:
                    coin_volume = 0
                    coins = get_coins_with_info()
                    for c in coins:
                        if c['symbol'] == symbol:
                            coin_volume = c['volume']
                            break
                    if side == "BUY":
                        max_price_buy = _BALANCE_CONFIG.get("max_price_buy", float('inf'))
                        max_volume_buy = _BALANCE_CONFIG.get("max_volume_buy", float('inf'))
                        if current_price > max_price_buy and coin_volume > max_volume_buy:
                            self.log(f"⚠️ {symbol} - Cả giá và volume đều không đạt điều kiện BUY")
                            self.stop_symbol(symbol, failed=True)
                            return False
                    else:
                        min_price_sell = _BALANCE_CONFIG.get("min_price_sell", 0.0)
                        min_volume_sell = _BALANCE_CONFIG.get("min_volume_sell", 0.0)
                        if current_price < min_price_sell and coin_volume < min_volume_sell:
                            self.log(f"⚠️ {symbol} - Cả giá và volume đều không đạt điều kiện SELL")
                            self.stop_symbol(symbol, failed=True)
                            return False

                step_size = get_step_size(symbol)
                min_qty = get_min_qty_from_cache(symbol)
                min_notional = get_min_notional_from_cache(symbol)

                qty = (required_usd * self.lev) / current_price
                if step_size > 0:
                    qty = math.floor(qty / step_size) * step_size
                    qty = round(qty, 8)

                if qty < min_qty:
                    self.log(f"❌ {symbol} - Khối lượng {qty} nhỏ hơn minQty {min_qty}")
                    self.stop_symbol(symbol, failed=True)
                    return False

                notional_value = qty * current_price
                if notional_value < min_notional:
                    self.log(f"❌ {symbol} - Giá trị danh nghĩa {notional_value:.2f} < {min_notional}")
                    self.stop_symbol(symbol, failed=True)
                    return False

                if qty <= 0:
                    self.log(f"❌ {symbol} - Khối lượng không hợp lệ")
                    self.stop_symbol(symbol, failed=True)
                    return False

                cancel_all_orders(symbol, self.api_key, self.api_secret)
                time.sleep(1)

                result = place_order(symbol, side, qty, self.api_key, self.api_secret)
                if result and 'orderId' in result:
                    executed_qty = float(result.get('executedQty', 0))
                    avg_price = float(result.get('avgPrice', current_price))
                    if executed_qty < 0:
                        self.log(f"❌ {symbol} - Lệnh không khớp")
                        self.stop_symbol(symbol, failed=True)
                        return False

                    self.symbol_data[symbol].update({
                        'entry': avg_price,
                        'entry_base': avg_price,
                        'qty': executed_qty if side == "BUY" else -executed_qty,
                        'side': side,
                        'position_open': True,
                        'status': "open",
                        'last_trade_time': time.time(),
                    })

                    # Khởi tạo theo dõi nến
                    self.last_candle_check[symbol] = 0

                    self.bot_coordinator.bot_has_coin(self.bot_id)
                    if hasattr(self, '_bot_manager') and self._bot_manager:
                        self._bot_manager.bot_coordinator.release_coin(symbol)

                    self.consecutive_failures = 0
                    message = (f"✅ <b>ĐÃ MỞ VỊ THẾ {symbol}</b>\n"
                               f"🤖 Bot: {self.bot_id}\n📌 Hướng: {side}\n"
                               f"🏷️ Entry: {self.symbol_data[symbol]['entry']:.4f}\n"
                               f"📊 Khối lượng: {abs(self.symbol_data[symbol]['qty']):.4f}\n"
                               f"💰 Đòn bẩy: {self.lev}x\n"
                               f"🎯 Thoát: Khi nến 15m ngược hướng")
                    self.log(message)
                    return True
                else:
                    error_msg = result.get('msg', 'Lỗi không xác định') if result else 'Không có phản hồi'
                    self.log(f"❌ {symbol} - Lỗi lệnh: {error_msg}")
                    self.stop_symbol(symbol, failed=True)
                    return False

            except Exception as e:
                self.log(f"❌ {symbol} - Lỗi mở vị thế: {str(e)}")
                self.stop_symbol(symbol, failed=True)
                return False

    # ---------- THOÁT LỆNH THEO NẾN 15 PHÚT ----------
    def _check_candle_exit_15m(self, symbol):
        """Kiểm tra nến 15 phút vừa đóng: nếu tín hiệu ngược hướng thì đóng lệnh"""
        if symbol not in self.symbol_data:
            return False
        data = self.symbol_data[symbol]
        if not data['position_open']:
            return False

        try:
            url = "https://fapi.binance.com/fapi/v1/klines"
            params = {"symbol": symbol.upper(), "interval": "15m", "limit": 1}
            kline_data = binance_api_request(url, params=params)
            if not kline_data or len(kline_data) == 0:
                return False
            curr_candle = kline_data[0]
            close_time = curr_candle[6]  # close time in milliseconds
            close_time_sec = close_time / 1000.0

            last = self.last_candle_check.get(symbol, 0)
            if close_time_sec <= last:
                return False

            # Nến mới đã đóng, cập nhật thời gian đã xử lý
            self.last_candle_check[symbol] = close_time_sec

            # Lấy 2 nến gần nhất để tính tín hiệu
            params2 = {"symbol": symbol.upper(), "interval": "15m", "limit": 2}
            klines = binance_api_request(url, params=params2)
            if not klines or len(klines) < 2:
                return False
            prev = klines[0]
            curr = klines[1]
            vol_prev = float(prev[5])
            vol_curr = float(curr[5])
            open_curr = float(curr[1])
            close_curr = float(curr[4])
            is_green = close_curr > open_curr

            if vol_prev > vol_curr:
                signal = "SELL" if is_green else "BUY"
            else:
                signal = "BUY" if is_green else "SELL"

            current_side = data['side']
            if signal is not None and signal != current_side:
                self.log(f"🕯️ {symbol} - Nến 15m đóng ngược hướng ({signal} vs {current_side}), đóng lệnh")
                if self._close_symbol_position(symbol, reason="(Candle 15m opposite)"):
                    self._blacklist_and_stop_symbol(symbol, reason="Candle 15m opposite")
                return True
            else:
                # Cùng hướng, giữ lệnh
                self.log(f"🕯️ {symbol} - Nến 15m đóng cùng hướng ({signal} vs {current_side}), giữ lệnh")
                return False
        except Exception as e:
            logger.error(f"Lỗi kiểm tra nến thoát 15m {symbol}: {e}")
            return False

    # ---------- ĐÓNG LỆNH ----------
    def _close_symbol_position(self, symbol, reason=""):
        with self.symbol_locks[symbol]:
            try:
                if symbol not in self.symbol_data:
                    return False
                if not self.symbol_data[symbol]['position_open']:
                    return False

                real_pos = self._force_check_position(symbol)
                if not real_pos:
                    self.log(f"ℹ️ {symbol} - API xác nhận không còn vị thế, reset trạng thái.")
                    self._reset_symbol_position(symbol)
                    return True

                qty = abs(float(real_pos.get('positionAmt', 0)))
                if qty == 0:
                    self.log(f"ℹ️ {symbol} - Vị thế đã đóng, reset.")
                    self._reset_symbol_position(symbol)
                    return True

                side = self.symbol_data[symbol]['side']
                close_side = "SELL" if side == "BUY" else "BUY"

                cancel_all_orders(symbol, self.api_key, self.api_secret)
                time.sleep(1)

                result = place_order(symbol, close_side, qty, self.api_key, self.api_secret)
                if result and 'orderId' in result:
                    self.log(f"🔴 Đã đóng vị thế {symbol} {reason}")
                    time.sleep(1)
                    self._reset_symbol_position(symbol)

                    if self.find_new_bot_after_close and not self.symbol:
                        self.status = "searching"
                    return True
                else:
                    self.log(f"❌ Đóng lệnh {symbol} thất bại")
                    return False

            except Exception as e:
                self.log(f"❌ Lỗi đóng vị thế {symbol}: {str(e)}")
                return False

    def _blacklist_and_stop_symbol(self, symbol, reason=""):
        if symbol not in self.active_symbols:
            return
        self.bot_coordinator.add_temp_blacklist(symbol, duration=300)
        self.log(f"⛔ {symbol} đã bị blacklist 5 phút do {reason}")
        self.stop_symbol(symbol, failed=False)

    # ---------- CÁC HÀM HỖ TRỢ ----------
    def _check_margin_safety(self):
        try:
            margin_balance, maint_margin, ratio = get_margin_safety_info(self.api_key, self.api_secret)
            if ratio is not None and ratio < self.margin_safety_threshold:
                self.log(f"🚫 CẢNH BÁO AN TOÀN KÝ QUỸ: tỷ lệ {ratio:.2f}x < {self.margin_safety_threshold}x")
                self.log("⛔ Đóng tất cả vị thế do margin thấp")
                for symbol in self.active_symbols.copy():
                    if self._close_symbol_position(symbol, reason="(Margin safety)"):
                        self._blacklist_and_stop_symbol(symbol, reason="Margin safety")
                return True
            return False
        except Exception as e:
            logger.error(f"Lỗi kiểm tra margin safety: {str(e)}")
            return False

    def check_global_positions(self):
        if hasattr(self, '_bot_manager') and self._bot_manager and hasattr(self._bot_manager, 'global_side_coordinator'):
            self.next_global_side = self._bot_manager.global_side_coordinator.get_next_side(
                self.api_key, self.api_secret
            )

    def get_next_side_based_on_comprehensive_analysis(self):
        if hasattr(self, '_bot_manager') and self._bot_manager and hasattr(self._bot_manager, 'global_side_coordinator'):
            return self._bot_manager.global_side_coordinator.get_next_side(self.api_key, self.api_secret)
        else:
            long_count = 0
            short_count = 0
            for sym, data in self.symbol_data.items():
                if data.get('position_open'):
                    if data['side'] == 'BUY':
                        long_count += 1
                    else:
                        short_count += 1
            if long_count > short_count:
                return "SELL"
            elif short_count > long_count:
                return "BUY"
            else:
                return random.choice(["BUY", "SELL"])

    def stop_symbol(self, symbol, failed=False):
        if symbol not in self.active_symbols:
            return False

        self.log(f"⛔ Đang dừng coin {symbol}...{' (lỗi)' if failed else ''}")

        if self.symbol_data.get(symbol, {}).get('position_open'):
            try:
                self._close_symbol_position(symbol, reason="(Stop by user)")
            except Exception as e:
                self.log(f"❌ Lỗi đóng vị thế khi dừng {symbol}: {str(e)}")

        try:
            self.ws_manager.remove_symbol(symbol)
        except Exception as e:
            self.log(f"❌ Lỗi dừng WebSocket {symbol}: {str(e)}")

        try:
            self.active_symbols.remove(symbol)
        except ValueError:
            self.log(f"⚠️ {symbol} không có trong active_symbols khi dừng")

        self.coin_manager.unregister_coin(symbol)

        # Xóa theo dõi nến
        self.last_candle_check.pop(symbol, None)

        if failed:
            if hasattr(self, '_bot_manager') and self._bot_manager:
                try:
                    self._bot_manager.bot_coordinator.release_coin(symbol)
                    self._bot_manager.bot_coordinator.add_temp_blacklist(symbol, duration=1800)
                except Exception as e:
                    self.log(f"❌ Lỗi release/blacklist {symbol}: {str(e)}")
            self.consecutive_failures += 1
            cooldown = min(60, 5 * self.consecutive_failures)
            self.failure_cooldown_until = time.time() + cooldown
            self.log(f"⏳ Thất bại lần {self.consecutive_failures}, nghỉ {cooldown}s trước khi tìm coin mới")
        else:
            self.consecutive_failures = 0

        if not self.active_symbols:
            self.bot_coordinator.bot_lost_coin(self.bot_id)
            self.bot_coordinator.finish_coin_search(self.bot_id)
            self.status = "searching"
            self.log("🔍 Chuyển sang trạng thái tìm coin mới")

        self.log(f"✅ Đã dừng coin {symbol}")
        return True

    def stop_all_symbols(self):
        count = 0
        for symbol in self.active_symbols.copy():
            if self.stop_symbol(symbol):
                count += 1
        return count

    def stop(self):
        self.log("🔴 Bot đang dừng...")
        self._stop = True
        self.stop_all_symbols()
        if self.bot_coordinator:
            self.bot_coordinator.remove_bot(self.bot_id)
        self.log("✅ Bot đã dừng")

    def log(self, message):
        logger.info(f"[{self.bot_id}] {message}")
        if self.telegram_bot_token and self.telegram_chat_id:
            send_telegram(f"<b>{self.bot_id}</b>: {message}",
                         chat_id=self.telegram_chat_id,
                         bot_token=self.telegram_bot_token,
                         default_chat_id=self.telegram_chat_id)

class GlobalMarketBot(BaseBot):
    pass

# ========== BotManager (CẬP NHẬT LUỒNG TẠO BOT, BỎ TP/SL, ROI, PYRAMIDING) ==========
class BotManager:
    def __init__(self, api_key=None, api_secret=None, telegram_bot_token=None, telegram_chat_id=None):
        self.ws_manager = WebSocketManager()
        self.bots = {}
        self.running = True
        self.start_time = time.time()
        self.user_states = {}

        self.api_key = api_key
        self.api_secret = api_secret
        self.telegram_bot_token = telegram_bot_token
        self.telegram_chat_id = telegram_chat_id

        self.bot_coordinator = BotExecutionCoordinator()
        self.coin_manager = CoinManager()
        self.symbol_locks = defaultdict(threading.RLock)
        self.global_side_coordinator = GlobalSideCoordinator()

        if api_key and api_secret:
            self._verify_api_connection()
            self.log("🟢 HỆ THỐNG BOT TÍN HIỆU 2 NẾN 15 PHÚT - KHÔNG TP/SL - THOÁT THEO NẾN")
            self._initialize_cache()
            self._cache_thread = threading.Thread(target=self._cache_updater, daemon=True, name='cache_updater')
            self._cache_thread.start()
            self.telegram_thread = threading.Thread(target=self._telegram_listener, daemon=True, name='telegram')
            self.telegram_thread.start()
            if self.telegram_chat_id:
                self.send_main_menu(self.telegram_chat_id)
        else:
            self.log("⚡ BotManager đã khởi động ở chế độ không cấu hình")

    def _initialize_cache(self):
        logger.info("🔄 Hệ thống đang khởi tạo cache...")
        if refresh_coins_cache():
            update_coins_volume()
            update_coins_price()
            coins_count = len(_COINS_CACHE.get_data())
            logger.info(f"✅ Hệ thống đã khởi tạo cache {coins_count} coin")
        else:
            logger.error("❌ Hệ thống không thể khởi tạo cache")

    def _cache_updater(self):
        while self.running:
            try:
                time.sleep(300)
                logger.info("🔄 Tự động làm mới cache...")
                refresh_coins_cache()
                update_coins_volume()
                update_coins_price()
            except Exception as e:
                logger.error(f"❌ Lỗi làm mới cache tự động: {str(e)}")

    def _verify_api_connection(self):
        try:
            balance = get_balance(self.api_key, self.api_secret)
            if balance is None:
                self.log("❌ LỖI: Không thể kết nối đến API Binance. Kiểm tra API Key/Secret, VPN, internet.")
                return False
            else:
                self.log(f"✅ Kết nối Binance thành công! Số dư: {balance:.2f} USDT/USDC")
                return True
        except Exception as e:
            self.log(f"❌ Lỗi kiểm tra kết nối: {str(e)}")
            return False

    def get_position_summary(self):
        try:
            positions = get_positions(api_key=self.api_key, api_secret=self.api_secret)
            long_count = sum(1 for p in positions if float(p.get('positionAmt', 0)) > 0)
            short_count = sum(1 for p in positions if float(p.get('positionAmt', 0)) < 0)
            long_pnl = sum(float(p.get('unRealizedProfit', 0)) for p in positions if float(p.get('positionAmt', 0)) > 0)
            short_pnl = sum(float(p.get('unRealizedProfit', 0)) for p in positions if float(p.get('positionAmt', 0)) < 0)
            total_unrealized_pnl = long_pnl + short_pnl

            bot_details = []
            total_bots_with_coins, trading_bots = 0, 0
            balance_bots = 0

            sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
            for idx, (bot_id, bot) in enumerate(sorted_bots, start=1):
                has_coin = len(bot.active_symbols) > 0 if hasattr(bot, 'active_symbols') else False
                is_trading = False
                if has_coin and hasattr(bot, 'symbol_data'):
                    for symbol, data in bot.symbol_data.items():
                        if data.get('position_open', False):
                            is_trading = True
                            break
                if has_coin:
                    total_bots_with_coins += 1
                if is_trading:
                    trading_bots += 1
                if hasattr(bot, 'enable_balance_orders') and bot.enable_balance_orders:
                    balance_bots += 1

                bot_details.append({
                    'index': idx,
                    'bot_id': bot_id,
                    'has_coin': has_coin,
                    'is_trading': is_trading,
                    'symbols': bot.active_symbols if hasattr(bot, 'active_symbols') else [],
                    'symbol_data': bot.symbol_data if hasattr(bot, 'symbol_data') else {},
                    'status': bot.status,
                    'leverage': bot.lev,
                    'percent': bot.percent,
                    'balance_orders': "BẬT" if hasattr(bot, 'enable_balance_orders') and bot.enable_balance_orders else "TẮT",
                })

            summary = "📊 **THỐNG KÊ CHI TIẾT - HỆ THỐNG TÍN HIỆU 2 NẾN 15 PHÚT (USDT/USDC)**\n\n"

            cache_stats = _COINS_CACHE.get_stats()
            coins_in_cache = cache_stats['count']
            last_price_update = cache_stats['last_price_update']
            update_time = time.ctime(last_price_update) if last_price_update > 0 else "Chưa cập nhật"

            summary += f"🗂️ **CACHE HỆ THỐNG**: {coins_in_cache} coin | Cập nhật: {update_time}\n"
            summary += f"⚖️ **BOT CÂN BẰNG**: {balance_bots}/{len(self.bots)} bot\n\n"

            total_balance, available_balance = get_total_and_available_balance(self.api_key, self.api_secret)
            margin_balance = get_margin_balance(self.api_key, self.api_secret)
            if total_balance is not None:
                summary += f"💰 **TỔNG SỐ DƯ**: {total_balance:.2f} USDT/USDC\n"
                summary += f"💰 **SỐ DƯ KHẢ DỤNG**: {available_balance:.2f} USDT/USDC\n"
                summary += f"💰 **SỐ DƯ KÝ QUỸ**: {margin_balance:.2f} USDT/USDC\n"
                summary += f"📈 **Tổng PnL**: {total_unrealized_pnl:.2f} USDT/USDC\n\n"
            else:
                summary += f"💰 **SỐ DƯ**: ❌ Lỗi kết nối\n\n"

            summary += f"🤖 **SỐ BOT HỆ THỐNG**: {len(self.bots)} bot | {total_bots_with_coins} bot có coin | {trading_bots} bot đang giao dịch\n\n"
            summary += f"📈 **PHÂN TÍCH PnL VÀ KHỐI LƯỢNG**:\n"
            summary += f"   📊 Số lượng: LONG={long_count} | SHORT={short_count}\n"
            summary += f"   💰 PnL: LONG={long_pnl:.2f} | SHORT={short_pnl:.2f}\n"
            summary += f"   ⚖️ Chênh lệch: {abs(long_pnl - short_pnl):.2f}\n\n"

            queue_info = self.bot_coordinator.get_queue_info()
            summary += f"🎪 **THÔNG TIN HÀNG ĐỢI (FIFO)**\n"
            summary += f"• Bot đang tìm coin: {queue_info['current_finding'] or 'Không có'}\n"
            summary += f"• Bot trong hàng đợi: {queue_info['queue_size']}\n"
            summary += f"• Bot có coin: {len(queue_info['bots_with_coins'])}\n"
            summary += f"• Coin đã phân phối: {queue_info['found_coins_count']}\n\n"

            if bot_details:
                summary += "📋 **CHI TIẾT BOT**:\n"
                for bot in bot_details:
                    status_emoji = "🟢" if bot['is_trading'] else "🟡" if bot['has_coin'] else "🔴"
                    balance_emoji = "⚖️" if bot['balance_orders'] == "BẬT" else ""
                    summary += f"{status_emoji} **bot_{bot['index']}** {balance_emoji}\n"
                    summary += f"   💰 Đòn bẩy: {bot['leverage']}x | Vốn: {bot['percent']}% | Cân bằng: {bot['balance_orders']}\n"
                    if bot['symbols']:
                        for symbol in bot['symbols']:
                            symbol_info = bot['symbol_data'].get(symbol, {})
                            status = "🟢 Đang giao dịch" if symbol_info.get('position_open') else "🟡 Chờ tín hiệu"
                            side = symbol_info.get('side', '')
                            qty = symbol_info.get('qty', 0)
                            summary += f"   🔗 {symbol} | {status}"
                            if side:
                                summary += f" | {side} {abs(qty):.4f}"
                            summary += "\n"
                    else:
                        summary += f"   🔍 Đang tìm coin...\n"
                    summary += "\n"

            return summary
        except Exception as e:
            return f"❌ Lỗi thống kê: {str(e)}"

    def log(self, message):
        important_keywords = ['❌', '✅', '⛔', '💰', '📈', '📊', '🎯', '🛡️', '🔴', '🟢', '⚠️', '🚫', '🔄']
        if any(keyword in message for keyword in important_keywords):
            logger.warning(f"[HỆ THỐNG] {message}")
            if self.telegram_bot_token and self.telegram_chat_id:
                send_telegram(f"<b>HỆ THỐNG</b>: {message}",
                             chat_id=self.telegram_chat_id,
                             bot_token=self.telegram_bot_token,
                             default_chat_id=self.telegram_chat_id)

    def send_main_menu(self, chat_id):
        welcome = (
            "🤖 <b>BOT GIAO DỊCH FUTURES - TÍN HIỆU 2 NẾN 15 PHÚT (USDT/USDC)</b>\n\n"
            "🎯 <b>CƠ CHẾ HOẠT ĐỘNG:</b>\n"
            "• So sánh khối lượng 2 nến 15 phút gần nhất:\n"
            "  - Nếu vol_prev > vol_curr → vào lệnh NGƯỢC hướng nến hiện tại\n"
            "  - Nếu vol_prev ≤ vol_curr → vào lệnh CÙNG hướng nến hiện tại\n"
            "• Kết hợp với cân bằng số lượng lệnh BUY/SELL toàn cục\n\n"
            "🔄 <b>QUẢN LÝ LỆNH:</b>\n"
            "• KHÔNG dùng TP/SL. Thoát lệnh khi một nến 15 phút đóng và tín hiệu của nến đó\n"
            "  NGƯỢC với hướng vị thế đang giữ.\n"
            "• Nếu tín hiệu cùng hướng → giữ lệnh, chờ nến tiếp theo.\n\n"
            "⚖️ <b>LỌC COIN (nếu bật cân bằng lệnh):</b>\n"
            "• MUA: giá ≤ max_price_buy, volume ≤ max_volume_buy\n"
            "• BÁN: giá ≥ min_price_sell, volume ≥ min_volume_sell\n\n"
            "📌 <b>LƯU Ý:</b> Không cài đặt TP/SL, không ROI trigger, không nhồi lệnh."
        )
        send_telegram(welcome, chat_id=chat_id, reply_markup=create_main_menu(),
                     bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

    def add_bot(self, symbol, lev, percent, strategy_type, bot_count=1, **kwargs):
        if not self.api_key or not self.api_secret:
            self.log("❌ API Key chưa được cài đặt trong BotManager")
            return False

        if not self._verify_api_connection():
            self.log("❌ KHÔNG THỂ KẾT NỐI VỚI BINANCE - KHÔNG THỂ TẠO BOT")
            return False

        bot_mode = kwargs.get('bot_mode', 'static')
        enable_balance_orders = kwargs.get('enable_balance_orders', True)
        max_price_buy = kwargs.get('max_price_buy', float('inf'))
        max_volume_buy = kwargs.get('max_volume_buy', float('inf'))
        min_price_sell = kwargs.get('min_price_sell', 0.0)
        min_volume_sell = kwargs.get('min_volume_sell', 0.0)

        created_count = 0
        for i in range(bot_count):
            if bot_mode == 'static' and symbol:
                bot_id = f"STATIC_{strategy_type}_{int(time.time())}_{i}"
            else:
                bot_id = f"DYNAMIC_{strategy_type}_{int(time.time())}_{i}"
            if bot_id in self.bots:
                continue

            bot = BaseBot(
                symbol, lev, percent, self.ws_manager,
                self.api_key, self.api_secret, self.telegram_bot_token, self.telegram_chat_id,
                coin_manager=self.coin_manager, symbol_locks=self.symbol_locks,
                bot_coordinator=self.bot_coordinator, bot_id=bot_id, max_coins=1,
                enable_balance_orders=enable_balance_orders,
                max_price_buy=max_price_buy, max_volume_buy=max_volume_buy,
                min_price_sell=min_price_sell, min_volume_sell=min_volume_sell,
                strategy_name=strategy_type
            )
            bot._bot_manager = self
            bot.coin_finder.set_bot_manager(self)
            self.bots[bot_id] = bot
            created_count += 1

        if created_count > 0:
            balance_info = ""
            if enable_balance_orders:
                balance_info = (f"\n⚖️ <b>CÂN BẰNG LỆNH: BẬT</b>\n"
                                f"• MUA: giá ≤ {max_price_buy} USDT, volume ≤ {max_volume_buy}\n"
                                f"• BÁN: giá ≥ {min_price_sell} USDT, volume ≥ {min_volume_sell}\n")
            success_msg = (f"✅ <b>ĐÃ TẠO {created_count} BOT TÍN HIỆU 2 NẾN 15 PHÚT</b>\n\n"
                           f"🎯 Chiến lược: {strategy_type}\n💰 Đòn bẩy: {lev}x\n"
                           f"📈 % Số dư: {percent}%\n"
                           f"🔧 Chế độ: {bot_mode}\n🔢 Số bot: {created_count}\n")
            if bot_mode == 'static' and symbol:
                success_msg += f"🔗 Coin ban đầu: {symbol}\n"
            else:
                success_msg += f"🔗 Coin: Tự động tìm (USDT/USDC) - dùng tín hiệu 2 nến 15 phút\n"
            success_msg += balance_info
            self.log(success_msg)
            return True
        else:
            self.log("❌ Không thể tạo bot")
            return False

    def stop_coin(self, symbol):
        stopped_count = 0
        symbol = symbol.upper()
        for bot_id, bot in self.bots.items():
            if hasattr(bot, 'stop_symbol') and symbol in bot.active_symbols:
                if bot.stop_symbol(symbol): stopped_count += 1
        if stopped_count > 0:
            self.log(f"✅ Đã dừng coin {symbol} trong {stopped_count} bot")
            return True
        else:
            self.log(f"❌ Không tìm thấy coin {symbol} trong bot nào")
            return False

    def get_coin_management_keyboard(self):
        all_coins = set()
        for bot in self.bots.values():
            if hasattr(bot, 'active_symbols'):
                all_coins.update(bot.active_symbols)
        if not all_coins: return None
        keyboard = []
        row = []
        for coin in sorted(list(all_coins))[:12]:
            row.append({"text": f"⛔ Coin: {coin}"})
            if len(row) == 2:
                keyboard.append(row)
                row = []
        if row: keyboard.append(row)
        keyboard.append([{"text": "⛔ DỪNG TẤT CẢ COIN"}])
        keyboard.append([{"text": "❌ Hủy bỏ"}])
        return {"keyboard": keyboard, "resize_keyboard": True, "one_time_keyboard": True}

    def stop_bot_symbol(self, bot_id, symbol):
        bot = self.bots.get(bot_id)
        if bot and hasattr(bot, 'stop_symbol'):
            success = bot.stop_symbol(symbol)
            if success: self.log(f"⛔ Đã dừng coin {symbol} trong bot {bot_id}")
            return success
        return False

    def stop_all_bot_symbols(self, bot_id):
        bot = self.bots.get(bot_id)
        if bot and hasattr(bot, 'stop_all_symbols'):
            stopped_count = bot.stop_all_symbols()
            self.log(f"⛔ Đã dừng {stopped_count} coin trong bot {bot_id}")
            return stopped_count
        return 0

    def stop_all_coins(self):
        self.log("⛔ Đang dừng tất cả coin trong tất cả bot...")
        total_stopped = 0
        for bot_id, bot in self.bots.items():
            if hasattr(bot, 'stop_all_symbols'):
                stopped_count = bot.stop_all_symbols()
                total_stopped += stopped_count
                self.log(f"⛔ Đã dừng {stopped_count} coin trong bot {bot_id}")
        self.log(f"✅ Đã dừng tổng cộng {total_stopped} coin, hệ thống vẫn chạy")
        return total_stopped

    def stop_bot(self, bot_id):
        bot = self.bots.get(bot_id)
        if bot:
            bot.stop()
            self.bot_coordinator.remove_bot(bot_id)
            del self.bots[bot_id]
            self.log(f"🔴 Đã dừng bot {bot_id}")
            return True
        return False

    def stop_all(self):
        self.log("🔴 Đang dừng tất cả bot...")
        for bot_id in list(self.bots.keys()):
            self.stop_bot(bot_id)
        self.log("🔴 Đã dừng tất cả bot, hệ thống vẫn chạy")

    def _telegram_listener(self):
        last_update_id = 0
        executor = ThreadPoolExecutor(max_workers=4, thread_name_prefix='tg_handler')
        while self.running and self.telegram_bot_token:
            try:
                url = f"https://api.telegram.org/bot{self.telegram_bot_token}/getUpdates?offset={last_update_id+1}&timeout=30"
                response = requests.get(url, timeout=35)
                if response.status_code == 200:
                    data = response.json()
                    if data.get('ok'):
                        for update in data['result']:
                            update_id = update['update_id']
                            if update_id > last_update_id:
                                last_update_id = update_id
                                executor.submit(self._handle_telegram_message, update)
                time.sleep(0.1)
            except Exception as e:
                logger.error(f"Lỗi nghe Telegram: {str(e)}")
                time.sleep(1)
        executor.shutdown(wait=False)

    def _handle_telegram_message(self, update):
        try:
            message = update.get('message', {})
            chat_id = str(message.get('chat', {}).get('id'))
            text = message.get('text', '').strip()
            if chat_id != self.telegram_chat_id:
                return
            self._process_telegram_command(chat_id, text)
        except Exception as e:
            logger.error(f"Lỗi xử lý tin nhắn Telegram: {str(e)}")

    def _process_telegram_command(self, chat_id, text):
        user_state = self.user_states.get(chat_id, {})
        current_step = user_state.get('step')

        if text == "📊 Danh sách Bot":
            if not self.bots:
                send_telegram("🤖 Hiện không có bot nào đang chạy.", chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
                bot_list = "\n".join([f"• bot_{idx} - {'🟢' if b.status != 'searching' else '🔴'}" for idx, (_, b) in enumerate(sorted_bots, start=1)])
                send_telegram(f"📋 Danh sách Bot:\n{bot_list}", chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "📊 Thống kê":
            summary = self.get_position_summary()
            send_telegram(summary, chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "➕ Thêm Bot":
            self.user_states[chat_id] = {'step': 'waiting_bot_mode'}
            send_telegram("🤖 Chọn chế độ bot:", chat_id=chat_id, reply_markup=create_bot_mode_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⛔ Dừng Bot":
            if not self.bots:
                send_telegram("🤖 Hiện không có bot nào để dừng.", chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
                keyboard = {"keyboard": [[{"text": f"bot_{idx}"}] for idx, (_, _) in enumerate(sorted_bots, start=1)] + [[{"text": "❌ Hủy bỏ"}]],
                           "resize_keyboard": True, "one_time_keyboard": True}
                self.user_states[chat_id] = {'step': 'waiting_stop_bot'}
                send_telegram("⛔ Chọn bot cần dừng (theo số thứ tự):", chat_id=chat_id, reply_markup=keyboard,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⛔ Quản lý Coin":
            keyboard = self.get_coin_management_keyboard()
            if keyboard:
                self.user_states[chat_id] = {'step': 'waiting_stop_coin'}
                send_telegram("⛔ Chọn coin cần dừng:", chat_id=chat_id, reply_markup=keyboard,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("📭 Không có coin nào đang được theo dõi.", chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "📈 Vị thế":
            positions = get_positions(api_key=self.api_key, api_secret=self.api_secret)
            if not positions:
                send_telegram("📭 Không có vị thế nào đang mở.", chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                msg = "📈 **VỊ THẾ ĐANG MỞ**\n\n"
                for pos in positions:
                    amt = float(pos.get('positionAmt', 0))
                    if amt != 0:
                        symbol = pos['symbol']
                        entry = float(pos.get('entryPrice', 0))
                        pnl = float(pos.get('unRealizedProfit', 0))
                        side = "LONG" if amt > 0 else "SHORT"
                        msg += f"{symbol} | {side} | Entry: {entry:.4f} | PnL: {pnl:.2f}\n"
                send_telegram(msg, chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "💰 Số dư":
            total, available = get_total_and_available_balance(self.api_key, self.api_secret)
            margin = get_margin_balance(self.api_key, self.api_secret)
            if total is not None:
                msg = (f"💰 **SỐ DƯ**\n"
                       f"• Tổng số dư (USDT+USDC): {total:.2f}\n"
                       f"• Số dư khả dụng: {available:.2f}\n"
                       f"• Số dư ký quỹ: {margin:.2f}")
            else:
                msg = "❌ Không thể lấy số dư"
            send_telegram(msg, chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⚙️ Cấu hình":
            send_telegram("⚙️ Tính năng đang phát triển.", chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "🎯 Chiến lược":
            sort_status = "BẬT (volume giảm dần)" if _BALANCE_CONFIG.get('sort_by_volume', True) else "TẮT"
            send_telegram(f"🎯 Chiến lược hiện tại:\n"
                         f"• MUA: giá ≤ {_BALANCE_CONFIG.get('max_price_buy', '∞')} USDT, volume ≤ {_BALANCE_CONFIG.get('max_volume_buy', '∞')}\n"
                         f"• BÁN: giá ≥ {_BALANCE_CONFIG.get('min_price_sell', 0)} USDT, volume ≥ {_BALANCE_CONFIG.get('min_volume_sell', 0)}\n"
                         f"📊 Sắp xếp coin: {sort_status}",
                         chat_id=chat_id, bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⚖️ Cân bằng lệnh":
            self.user_states[chat_id] = {'step': 'waiting_balance_config'}
            send_telegram("⚖️ <b>CẤU HÌNH CÂN BẰNG LỆNH</b>\n\nChọn hành động:",
                         chat_id=chat_id, reply_markup=create_balance_config_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "❌ Hủy bỏ":
            self.user_states[chat_id] = {}
            send_telegram("❌ Đã hủy thao tác.", chat_id=chat_id, reply_markup=create_main_menu(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        # Luồng tạo bot (rút gọn, bỏ TP/SL, ROI, volume ratio, pyramiding)
        elif current_step == 'waiting_bot_mode':
            if text == "🤖 Bot Tĩnh - Coin cụ thể":
                user_state['bot_mode'] = 'static'
                user_state['step'] = 'waiting_symbol'
                send_telegram("🔗 Nhập tên coin (ví dụ: BTCUSDT) hoặc chọn từ danh sách:",
                             chat_id=chat_id, reply_markup=create_symbols_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text == "🔄 Bot Động - Tự tìm coin":
                user_state['bot_mode'] = 'dynamic'
                user_state['step'] = 'waiting_leverage'
                send_telegram("⚙️ Chọn đòn bẩy:", chat_id=chat_id, reply_markup=create_leverage_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("⚠️ Vui lòng chọn chế độ bot hợp lệ.", chat_id=chat_id,
                             reply_markup=create_bot_mode_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_symbol':
            if text != "❌ Hủy bỏ":
                user_state['symbol'] = text.upper()
                user_state['step'] = 'waiting_leverage'
                send_telegram("⚙️ Chọn đòn bẩy:", chat_id=chat_id, reply_markup=create_leverage_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_leverage':
            if text.endswith('x') and text != "❌ Hủy bỏ":
                try:
                    lev = int(text[:-1])
                    user_state['leverage'] = lev
                    user_state['step'] = 'waiting_percent'
                    send_telegram("📊 Chọn % số dư cho mỗi lệnh:", chat_id=chat_id, reply_markup=create_percent_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                except:
                    send_telegram("⚠️ Vui lòng chọn đòn bẩy hợp lệ.", chat_id=chat_id,
                                 reply_markup=create_leverage_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_percent':
            if text != "❌ Hủy bỏ":
                try:
                    percent = float(text)
                    user_state['percent'] = percent
                    # Sau % vốn, chuyển sang hỏi số bot (nếu bot động) hoặc hỏi cân bằng lệnh (nếu bot tĩnh)
                    if user_state.get('bot_mode') == 'static':
                        user_state['bot_count'] = 1
                        user_state['step'] = 'waiting_balance_orders'
                        send_telegram("⚖️ Bật cân bằng lệnh? (Bật/Tắt)", chat_id=chat_id,
                                     reply_markup=create_balance_config_keyboard(),
                                     bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    else:
                        user_state['step'] = 'waiting_bot_count'
                        send_telegram("🔢 Nhập số bot muốn tạo:", chat_id=chat_id,
                                     reply_markup=create_bot_count_keyboard(),
                                     bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                except:
                    send_telegram("⚠️ Vui lòng nhập số hợp lệ.", chat_id=chat_id,
                                 reply_markup=create_percent_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_bot_count':
            if text != "❌ Hủy bỏ":
                try:
                    bot_count = int(text)
                    user_state['bot_count'] = bot_count
                    user_state['step'] = 'waiting_balance_orders'
                    send_telegram("⚖️ Bật cân bằng lệnh? (Bật/Tắt)", chat_id=chat_id,
                                 reply_markup=create_balance_config_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                except:
                    send_telegram("⚠️ Vui lòng nhập số nguyên.", chat_id=chat_id,
                                 reply_markup=create_bot_count_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_balance_orders':
            if text == '⚖️ Bật cân bằng lệnh':
                user_state['enable_balance_orders'] = True
                user_state['step'] = 'waiting_max_price_buy'
                send_telegram("📈 Nhập GIÁ TỐI ĐA cho phép MUA (USDT) - hoặc '❌ Bỏ qua' nếu không giới hạn:",
                             chat_id=chat_id, reply_markup=create_max_price_buy_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text == '⚖️ Tắt cân bằng lệnh':
                user_state['enable_balance_orders'] = False
                self._finish_bot_creation(chat_id, user_state)
            else:
                send_telegram("⚠️ Vui lòng chọn Bật hoặc Tắt.", chat_id=chat_id,
                             reply_markup=create_balance_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_max_price_buy':
            if text == "❌ Bỏ qua":
                user_state['max_price_buy'] = float('inf')
            elif text != "❌ Hủy bỏ":
                try:
                    val = float(text)
                    if val <= 0:
                        raise ValueError
                    user_state['max_price_buy'] = val
                except:
                    send_telegram("⚠️ Vui lòng nhập số > 0.", chat_id=chat_id,
                                 reply_markup=create_max_price_buy_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    return
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            user_state['step'] = 'waiting_max_volume_buy'
            send_telegram("📊 Nhập KHỐI LƯỢNG 24h TỐI ĐA cho phép MUA (USDT) - hoặc '❌ Bỏ qua':",
                         chat_id=chat_id, reply_markup=create_max_volume_buy_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_max_volume_buy':
            if text == "❌ Bỏ qua":
                user_state['max_volume_buy'] = float('inf')
            elif text != "❌ Hủy bỏ":
                try:
                    val = float(text)
                    if val <= 0:
                        raise ValueError
                    user_state['max_volume_buy'] = val
                except:
                    send_telegram("⚠️ Vui lòng nhập số > 0.", chat_id=chat_id,
                                 reply_markup=create_max_volume_buy_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    return
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            user_state['step'] = 'waiting_min_price_sell'
            send_telegram("📉 Nhập GIÁ TỐI THIỂU cho phép BÁN (USDT) - hoặc '❌ Bỏ qua':",
                         chat_id=chat_id, reply_markup=create_min_price_sell_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_min_price_sell':
            if text == "❌ Bỏ qua":
                user_state['min_price_sell'] = 0.0
            elif text != "❌ Hủy bỏ":
                try:
                    val = float(text)
                    if val < 0:
                        raise ValueError
                    user_state['min_price_sell'] = val
                except:
                    send_telegram("⚠️ Vui lòng nhập số >= 0.", chat_id=chat_id,
                                 reply_markup=create_min_price_sell_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    return
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            user_state['step'] = 'waiting_min_volume_sell'
            send_telegram("📊 Nhập KHỐI LƯỢNG 24h TỐI THIỂU cho phép BÁN (USDT) - hoặc '❌ Bỏ qua':",
                         chat_id=chat_id, reply_markup=create_min_volume_sell_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_min_volume_sell':
            if text == "❌ Bỏ qua":
                user_state['min_volume_sell'] = 0.0
            elif text != "❌ Hủy bỏ":
                try:
                    val = float(text)
                    if val < 0:
                        raise ValueError
                    user_state['min_volume_sell'] = val
                except:
                    send_telegram("⚠️ Vui lòng nhập số >= 0.", chat_id=chat_id,
                                 reply_markup=create_min_volume_sell_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    return
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return

            update_balance_config(
                max_price_buy=user_state.get('max_price_buy', float('inf')),
                max_volume_buy=user_state.get('max_volume_buy', float('inf')),
                min_price_sell=user_state.get('min_price_sell', 0.0),
                min_volume_sell=user_state.get('min_volume_sell', 0.0),
                sort_by_volume=True
            )
            self._finish_bot_creation(chat_id, user_state)

        elif current_step == 'waiting_balance_config':
            if text == '⚖️ Bật cân bằng lệnh':
                updated = 0
                for bot in self.bots.values():
                    if hasattr(bot, 'enable_balance_orders'):
                        bot.enable_balance_orders = True
                        updated += 1
                send_telegram(f"✅ Đã BẬT cân bằng lệnh cho {updated} bot.", chat_id=chat_id,
                             reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                self.user_states[chat_id] = {}
            elif text == '⚖️ Tắt cân bằng lệnh':
                updated = 0
                for bot in self.bots.values():
                    if hasattr(bot, 'enable_balance_orders'):
                        bot.enable_balance_orders = False
                        updated += 1
                send_telegram(f"✅ Đã TẮT cân bằng lệnh cho {updated} bot.", chat_id=chat_id,
                             reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                self.user_states[chat_id] = {}
            elif text == '📊 Xem cấu hình cân bằng':
                sort_status = "BẬT (volume giảm dần)" if _BALANCE_CONFIG.get('sort_by_volume', True) else "TẮT"
                config_info = (
                    f"⚖️ <b>CẤU HÌNH CÂN BẰNG HIỆN TẠI</b>\n\n"
                    f"• MUA: giá ≤ {_BALANCE_CONFIG.get('max_price_buy', '∞')} USDT, volume ≤ {_BALANCE_CONFIG.get('max_volume_buy', '∞')}\n"
                    f"• BÁN: giá ≥ {_BALANCE_CONFIG.get('min_price_sell', 0)} USDT, volume ≥ {_BALANCE_CONFIG.get('min_volume_sell', 0)}\n"
                    f"• Sắp xếp coin: {sort_status}\n\n"
                    f"🔄 <b>CACHE HỆ THỐNG</b>\n"
                    f"• Số coin: {len(_COINS_CACHE.get_data())}\n"
                    f"• Cập nhật giá: {time.ctime(_COINS_CACHE.get_stats()['last_price_update'])}\n"
                    f"• Cập nhật volume: {time.ctime(_COINS_CACHE.get_stats()['last_volume_update'])}"
                )
                send_telegram(config_info, chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text == '🔄 Làm mới cache':
                if force_refresh_coin_cache():
                    send_telegram("✅ Đã làm mới cache coin thành công", chat_id=chat_id,
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                else:
                    send_telegram("❌ Không thể làm mới cache", chat_id=chat_id,
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_stop_bot':
            if text.startswith("bot_"):
                try:
                    idx = int(text.split("_")[1])
                    sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
                    if 1 <= idx <= len(sorted_bots):
                        bot_id = sorted_bots[idx-1][0]
                        self.stop_bot(bot_id)
                        send_telegram(f"✅ Đã dừng bot {text}", chat_id=chat_id, reply_markup=create_main_menu(),
                                     bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                        self.user_states[chat_id] = {}
                    else:
                        send_telegram("❌ Số thứ tự không hợp lệ.", chat_id=chat_id, reply_markup=create_main_menu(),
                                     bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                        self.user_states[chat_id] = {}
                except:
                    send_telegram("❌ Bot không tồn tại.", chat_id=chat_id, reply_markup=create_main_menu(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    self.user_states[chat_id] = {}
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_stop_coin':
            if text.startswith("⛔ Coin: "):
                coin = text.replace("⛔ Coin: ", "")
                self.stop_coin(coin)
                send_telegram(f"✅ Đã dừng coin {coin}", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                self.user_states[chat_id] = {}
            elif text == "⛔ DỪNG TẤT CẢ COIN":
                self.stop_all_coins()
                send_telegram("✅ Đã dừng tất cả coin", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                self.user_states[chat_id] = {}
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        else:
            self.send_main_menu(chat_id)

    def _finish_bot_creation(self, chat_id, user_state):
        try:
            bot_mode = user_state.get('bot_mode', 'static')
            leverage = user_state.get('leverage')
            percent = user_state.get('percent')
            symbol = user_state.get('symbol')
            bot_count = user_state.get('bot_count', 1)
            enable_balance_orders = user_state.get('enable_balance_orders', True)
            max_price_buy = user_state.get('max_price_buy', float('inf'))
            max_volume_buy = user_state.get('max_volume_buy', float('inf'))
            min_price_sell = user_state.get('min_price_sell', 0.0)
            min_volume_sell = user_state.get('min_volume_sell', 0.0)

            success = self.add_bot(
                symbol=symbol, lev=leverage, percent=percent, strategy_type="15mCandleSignal",
                bot_mode=bot_mode, bot_count=bot_count,
                enable_balance_orders=enable_balance_orders,
                max_price_buy=max_price_buy, max_volume_buy=max_volume_buy,
                min_price_sell=min_price_sell, min_volume_sell=min_volume_sell
            )

            if success:
                balance_info = " | ⚖️ Cân bằng: BẬT" if enable_balance_orders else " | ⚖️ Cân bằng: TẮT"
                filter_info = ""
                if enable_balance_orders:
                    filter_info = (f"\n📈 MUA: giá ≤ {max_price_buy} USDT, vol ≤ {max_volume_buy}"
                                   f"\n📉 BÁN: giá ≥ {min_price_sell} USDT, vol ≥ {min_volume_sell}")

                success_msg = (f"✅ <b>ĐÃ TẠO BOT TÍN HIỆU 2 NẾN 15 PHÚT THÀNH CÔNG</b>\n\n"
                               f"🤖 Chiến lược: 15m Candle Signal\n🔧 Chế độ: {bot_mode}\n"
                               f"🔢 Số bot: {bot_count}\n💰 Đòn bẩy: {leverage}x\n"
                               f"📊 % Số dư: {percent}%\n"
                               f"🎯 Thoát: Khi nến 15m ngược hướng{balance_info}{filter_info}")
                if bot_mode == 'static' and symbol:
                    success_msg += f"\n🔗 Coin: {symbol}"

                send_telegram(success_msg, chat_id=chat_id, reply_markup=create_main_menu(),
                            bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("❌ Lỗi tạo bot. Vui lòng thử lại.",
                            chat_id=chat_id, reply_markup=create_main_menu(),
                            bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

            self.user_states[chat_id] = {}
        except Exception as e:
            send_telegram(f"❌ Lỗi tạo bot: {str(e)}", chat_id=chat_id, reply_markup=create_main_menu(),
                        bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            self.user_states[chat_id] = {}

# ========== BỎ QUA SSL ==========
ssl._create_default_https_context = ssl._create_unverified_context


        print("Đã dừng hệ thống.")
