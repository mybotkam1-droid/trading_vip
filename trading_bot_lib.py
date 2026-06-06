
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

_BINANCE_LAST_REQUEST_TIME = 0
_BINANCE_RATE_LOCK = threading.RLock()
_BINANCE_MIN_INTERVAL = 0.2

_SYMBOL_BLACKLIST = {'BTCUSDT', 'BTCUSDC','ETHUSDT','ETHUSDC'}

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

def setup_logging():
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(module)s - %(message)s',
        handlers=[logging.StreamHandler(), logging.FileHandler('bot_errors.log')]
    )
    return logging.getLogger()

logger = setup_logging()

_SIGNAL_DATA_CACHE = {}
_SIGNAL_DATA_CACHE_TTL = 1.5
_SIGNAL_DATA_CACHE_MAX_SIZE = 1000

def _cleanup_signal_data_cache():
    try:
        now = time.time()
        expired = [k for k, v in list(_SIGNAL_DATA_CACHE.items())
                   if now - float(v.get('ts', 0) or 0) > max(_SIGNAL_DATA_CACHE_TTL * 10, 30)]
        for k in expired:
            _SIGNAL_DATA_CACHE.pop(k, None)
        if len(_SIGNAL_DATA_CACHE) > _SIGNAL_DATA_CACHE_MAX_SIZE:
            items = sorted(_SIGNAL_DATA_CACHE.items(), key=lambda kv: float(kv[1].get('ts', 0) or 0))
            for k, _ in items[:len(_SIGNAL_DATA_CACHE) - _SIGNAL_DATA_CACHE_MAX_SIZE]:
                _SIGNAL_DATA_CACHE.pop(k, None)
    except Exception:
        pass

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

def create_main_menu():
    return {
        "keyboard": [
            [{"text": "📊 Danh sách Bot"}, {"text": "📊 Thống kê"}],
            [{"text": "➕ Thêm Bot"}, {"text": "⛔ Dừng Bot"}],
            [{"text": "⛔ Quản lý Coin"}, {"text": "📈 Vị thế"}],
            [{"text": "💰 Số dư"}, {"text": "⚙️ Cấu hình"}],
            [{"text": "🎯 Chiến lược"}]
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

def create_tp_keyboard():
    return {
        "keyboard": [
            [{"text": "50"}, {"text": "100"}, {"text": "200"}],
            [{"text": "300"}, {"text": "500"}, {"text": "1000"}],
            [{"text": "❌ Bỏ qua (không TP)"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_sl_keyboard():
    return {
        "keyboard": [
            [{"text": "0"}, {"text": "50"}, {"text": "100"}],
            [{"text": "150"}, {"text": "200"}, {"text": "500"}],
            [{"text": "❌ Bỏ qua (không SL)"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_strategy_config_keyboard():
    return {
        "keyboard": [
            [{"text": "📊 Xem tham số chiến lược"}],
            [{"text": "✏️ Current timeframe"}, {"text": "✏️ Compare timeframe"}],
            [{"text": "✏️ Min elapsed seconds"}, {"text": "✏️ Speed reach factor"}],
            [{"text": "✏️ Speed up factor"}, {"text": "✏️ Speed down factor"}],
            [{"text": "✏️ Min body ratio"}, {"text": "✏️ Min range pct"}],
            [{"text": "✏️ Min body pct"}, {"text": "✏️ Flat zone lookback"}],
            [{"text": "✏️ Min box range pct"}],
            [{"text": "✏️ Low volume filter"}, {"text": "✏️ Min 24h volume"}],
            [{"text": "✏️ Profit protect ON/OFF"}, {"text": "✏️ Profit start ROI"}],
            [{"text": "✏️ Profit pullback ROI"}],
            [{"text": "♻️ Reset tham số chiến lược"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": False
    }


def create_strategy_value_keyboard():
    """Bàn phím nhập giá trị tham số chiến lược."""
    return {
        "keyboard": [
            [{"text": "0"}, {"text": "0.25"}, {"text": "0.50"}],
            [{"text": "0.80"}, {"text": "1.00"}, {"text": "1.20"}],
            [{"text": "1.50"}, {"text": "2.00"}, {"text": "3.00"}],
            [{"text": "1m"}, {"text": "3m"}, {"text": "5m"}, {"text": "15m"}],
            [{"text": "30m"}, {"text": "1h"}, {"text": "2h"}, {"text": "4h"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": True
    }


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

_BINANCE_INTERVAL_SECONDS = {
    '1m': 60.0, '3m': 180.0, '5m': 300.0, '15m': 900.0,
    '30m': 1800.0, '1h': 3600.0, '2h': 7200.0, '4h': 14400.0
}

def _normalize_interval(value):
    v = str(value or '1m').strip().lower()
    return v if v in _BINANCE_INTERVAL_SECONDS else '1m'

def _interval_seconds(interval=None):
    return float(_BINANCE_INTERVAL_SECONDS.get(_normalize_interval(interval), 60.0))

class StrategyConfig:
    """Cấu hình chiến lược SPEED 2 KHUNG NẾN: chỉ dùng tốc độ volume/time."""
    DEFAULTS = {
        'current_interval': '1m',
        'compare_interval': '1m',
        'timeframe_seconds': 60.0,
        'min_elapsed_seconds': 6.0,
        'volume_reach_factor': 0.50,   # giữ tên cũ, nhưng ý nghĩa mới: current_speed phải đạt tối thiểu 50% previous_speed
        'speed_up_factor': 1.00,       # current_speed > prev_speed * factor => tăng tốc
        'speed_down_factor': 1.00,     # current_speed < prev_speed * factor => giảm tốc (chỉ xác nhận khi nến hiện tại đã đóng)
        'body_ratio_min': 0.25,
        'min_range_pct': 0.08,
        'min_body_pct': 0.03,
        'flat_zone_lookback': 5,
        'min_box_range_pct': 0.15,
        'low_volume_filter_enabled': 1.0,
        'min_24h_volume': 10000000.0,
        'profit_protect_enabled': 1.0,
        'profit_protect_start_roi': 10.0,
        'profit_protect_pullback_roi': 8.0,
        'max_reverse_count': 10,
    }
    INT_KEYS = {'max_reverse_count', 'flat_zone_lookback'}
    STRING_KEYS = {'current_interval', 'compare_interval', 'signal_interval'}

    def __init__(self):
        self._config = self.DEFAULTS.copy()
        self._lock = threading.RLock()

    def get(self, key, default=None):
        with self._lock:
            if key == 'signal_interval':
                return self._config.get('current_interval', default)
            return self._config.get(key, default)

    def get_all(self):
        with self._lock:
            d = self._config.copy()
            d['signal_interval'] = d.get('current_interval', '1m')
            return d

    def update(self, **kwargs):
        with self._lock:
            for key, value in kwargs.items():
                if key == 'signal_interval':
                    key = 'current_interval'
                if key in self._config and value is not None:
                    if key in self.STRING_KEYS:
                        value = _normalize_interval(value)
                        self._config[key] = value
                        if key == 'current_interval':
                            self._config['timeframe_seconds'] = _interval_seconds(value)
                    elif key in self.INT_KEYS:
                        self._config[key] = int(float(value))
                    else:
                        self._config[key] = float(value)
        return self.get_all()

    def reset(self):
        with self._lock:
            self._config = self.DEFAULTS.copy()
        return self.get_all()

_STRATEGY_CONFIG = StrategyConfig()

def get_strategy_config_text():
    c = _STRATEGY_CONFIG.get_all()
    current_interval = _normalize_interval(c.get('current_interval', '1m'))
    compare_interval = _normalize_interval(c.get('compare_interval', '1m'))
    return (
        "🎯 <b>THAM SỐ SPEED 2 KHUNG NẾN</b>\n\n"
        f"• Current candle timeframe: {current_interval} ({_interval_seconds(current_interval):.0f}s)\n"
        f"• Compare closed candle timeframe: {compare_interval} ({_interval_seconds(compare_interval):.0f}s)\n"
        f"• Min elapsed seconds: {c.get('min_elapsed_seconds', 6.0):.1f}s\n"
        f"• Speed reach factor: {c.get('volume_reach_factor', 0.5):.2f}x tốc độ nến so sánh\n"
        f"• Speed up factor: {c.get('speed_up_factor', 1.0):.2f}x\n"
        f"• Speed down factor: {c.get('speed_down_factor', 1.0):.2f}x (chỉ xét khi nến hiện tại đóng)\n"
        f"• Min body ratio: {c.get('body_ratio_min', 0.25):.2f}\n"
        f"• Min range pct: {c.get('min_range_pct', 0.08):.3f}%\n"
        f"• Min body pct: {c.get('min_body_pct', 0.03):.3f}%\n"
        f"• Flat zone: lookback {int(c.get('flat_zone_lookback', 5))} nến | min box range {c.get('min_box_range_pct', 0.15):.3f}%\n"
        f"• Low volume filter: {'ON' if c.get('low_volume_filter_enabled', 1.0) >= 0.5 else 'OFF'} | min 24h volume: {c.get('min_24h_volume', 0):,.0f}\n"
        f"• Hút lực từ đỉnh: {'ON' if float(c.get('profit_protect_enabled', 1.0)) >= 0.5 else 'OFF'} | start {c.get('profit_protect_start_roi', 10.0):.1f}% ROI | tụt {c.get('profit_protect_pullback_roi', 8.0):.1f}% ROI thì đóng\n\n"
        "💰 <b>QUẢN LÝ VỐN</b>\n"
        "• Mỗi lệnh, kể cả đảo chiều: tính theo % số dư margin hiện tại.\n"
        "• TP/SL tính theo ROI đã nhân đòn bẩy.\n\n"
        "Luồng tín hiệu mới:\n"
        "1) Lấy nến hiện tại theo Current timeframe và nến đã đóng gần nhất theo Compare timeframe.\n"
        "2) Tốc độ = volume / thời gian. Nến hiện tại dùng elapsed thực tế, nến đã đóng dùng độ dài khung nến.\n"
        "3) Điều kiện tăng tốc: current_speed = volume hiện tại / thời gian đã chạy; previous_speed = tốc độ nến so sánh / độ dài khung nến. Không so raw volume giữa 1m và 15m/1h.\n"
        "4) Hai nến cùng chiều + tăng tốc → vào theo hướng nến hiện tại.\n"
        "5) Hai nến cùng chiều + giảm tốc → chỉ xác nhận khi nến hiện tại đã đóng, rồi vào ngược hướng nến hiện tại.\n"
        "6) Hai nến khác chiều + nến hiện tại tăng tốc → vào theo hướng nến hiện tại.\n"
        "7) Còn lại None. Khi đóng để đảo chiều thì đóng và đảo luôn, không kiểm tra lại lần hai."
    )

def _candle_direction(open_price, close_price):
    if close_price > open_price:
        return "BUY"
    if close_price < open_price:
        return "SELL"
    return None

def _opposite_side(side):
    if side == "BUY":
        return "SELL"
    if side == "SELL":
        return "BUY"
    return None

def _safe_progress(candle, timeframe_seconds=None):
    timeframe_seconds = timeframe_seconds or _STRATEGY_CONFIG.get('timeframe_seconds', 60.0)
    try:
        open_ms = int(candle.get('time', 0)) if isinstance(candle, dict) else int(candle[0])
        open_ts = open_ms / 1000.0 if open_ms > 10_000_000_000 else float(open_ms)
        elapsed = max(0.0, time.time() - open_ts)
        return max(0.001, min(1.0, elapsed / float(timeframe_seconds)))
    except Exception:
        return 1.0

def _candle_get(c, key, idx, default=0.0):
    try:
        return float(c.get(key, default)) if isinstance(c, dict) else float(c[idx])
    except Exception:
        return float(default)

def _is_not_sideway_candle(open_price, close_price, high_price, low_price, min_body_ratio=None):
    """Giữ tương thích tên cũ: True nếu nến đủ thân/range và không bị bẹt."""
    ok, info = _is_tradeable_candle(open_price, close_price, high_price, low_price, min_body_ratio=min_body_ratio)
    return ok, float(info.get('body_ratio', 0.0) or 0.0)


def _is_tradeable_candle(open_price, close_price, high_price, low_price, min_body_ratio=None):
    """Lọc nến không chỉ theo doji mà còn theo độ dài thật."""
    try:
        cfg = _STRATEGY_CONFIG.get_all()
        o = float(open_price)
        c = float(close_price)
        h = float(high_price)
        l = float(low_price)
        if o <= 0:
            return False, {'reason': 'bad_open'}
        rng = h - l
        body = abs(c - o)
        if rng <= 0:
            return False, {'reason': 'zero_range'}
        body_ratio = body / rng
        range_pct = rng / o * 100.0
        body_pct = body / o * 100.0
        min_body_ratio = float(cfg.get('body_ratio_min', 0.25) if min_body_ratio is None else min_body_ratio)
        min_range_pct = float(cfg.get('min_range_pct', 0.08))
        min_body_pct = float(cfg.get('min_body_pct', 0.03))
        if body_ratio < min_body_ratio:
            return False, {'reason': 'doji_body_ratio', 'body_ratio': body_ratio, 'range_pct': range_pct, 'body_pct': body_pct}
        if range_pct < min_range_pct:
            return False, {'reason': 'range_too_short', 'body_ratio': body_ratio, 'range_pct': range_pct, 'body_pct': body_pct}
        if body_pct < min_body_pct:
            return False, {'reason': 'body_pct_too_small', 'body_ratio': body_ratio, 'range_pct': range_pct, 'body_pct': body_pct}
        return True, {'reason': 'ok', 'body_ratio': body_ratio, 'range_pct': range_pct, 'body_pct': body_pct}
    except Exception as e:
        return False, {'reason': f'error_{type(e).__name__}'}


def _is_flat_zone(candles, current_price=None):
    """True nếu cụm nến đóng gần nhất quá bẹt dù từng cây không phải doji."""
    try:
        cfg = _STRATEGY_CONFIG.get_all()
        lookback = int(cfg.get('flat_zone_lookback', 5))
        if lookback <= 1:
            return False, {'reason': 'disabled'}
        if not candles or len(candles) < lookback:
            return False, {'reason': 'not_enough_history', 'have': len(candles or []), 'need': lookback}
        recent = list(candles)[-lookback:]
        highs = [_candle_get(c, 'high', 2) for c in recent]
        lows = [_candle_get(c, 'low', 3) for c in recent]
        zone_high = max(highs)
        zone_low = min(lows)
        ref_price = float(current_price or _candle_get(recent[-1], 'close', 4) or 0)
        if ref_price <= 0:
            return False, {'reason': 'bad_ref_price'}
        box_range_pct = (zone_high - zone_low) / ref_price * 100.0
        min_box = float(cfg.get('min_box_range_pct', 0.15))
        if box_range_pct < min_box:
            return True, {'reason': 'flat_zone', 'box_range_pct': box_range_pct, 'min_box_range_pct': min_box, 'lookback': lookback}
        return False, {'reason': 'ok', 'box_range_pct': box_range_pct, 'min_box_range_pct': min_box, 'lookback': lookback}
    except Exception as e:
        return False, {'reason': f'error_{type(e).__name__}'}


def _history_candle_direction(candle):
    try:
        o = _candle_get(candle, 'open', 1)
        c = _candle_get(candle, 'close', 4)
        return _candle_direction(o, c)
    except Exception:
        return None

def _majority_direction(candles):
    buys = 0
    sells = 0
    for c in candles:
        d = _history_candle_direction(c)
        if d == 'BUY':
            buys += 1
        elif d == 'SELL':
            sells += 1
    if buys > sells:
        return 'BUY'
    if sells > buys:
        return 'SELL'
    return None

def _volume_speed(candle):
    return max(0.0, _candle_get(candle, 'volume', 5))

def _near_highest(value, values, tolerance):
    if not values:
        return False
    return float(value) >= max(values) * (1.0 - float(tolerance))

def _near_lowest(value, values, tolerance):
    if not values:
        return False
    return float(value) <= min(values) * (1.0 + float(tolerance))

def _score_signal_parts(open_curr, current_price, high_curr, low_curr, volume_curr,
                        prev_candle, market_candle=None, progress=1.0,
                        mode='entry', recent_1m_history=None, market_history=None, current_is_final=False):
    """
    Chiến lược SPEED 2 KHUNG NẾN:
    - Nến hiện tại theo current_interval, tốc độ = volume_current / elapsed_seconds.
    - Nến so sánh là nến đã đóng gần nhất theo compare_interval, tốc độ = volume_prev / compare_interval_seconds.
    - 3 trường hợp:
      1) Cùng chiều + tăng tốc => theo hướng nến hiện tại.
      2) Cùng chiều + giảm tốc => đảo ngược hướng nến hiện tại.
      3) Khác chiều + nến hiện tại tăng tốc => theo hướng nến hiện tại.
      Còn lại None.
    """
    try:
        cfg = _STRATEGY_CONFIG.get_all()
        current_interval = _normalize_interval(cfg.get('current_interval', cfg.get('signal_interval', '1m')))
        compare_interval = _normalize_interval(cfg.get('compare_interval', current_interval))
        current_tf = _interval_seconds(current_interval)
        compare_tf = _interval_seconds(compare_interval)
        progress = max(float(progress), 0.001)
        elapsed = progress * current_tf
        min_elapsed = float(cfg.get('min_elapsed_seconds', 6.0))
        if elapsed < min_elapsed:
            return None, 0, f'elapsed_too_early_{elapsed:.1f}s need={min_elapsed:.1f}s', False

        if not prev_candle:
            return None, 0, 'missing_compare_closed_candle', False

        prev_open = _candle_get(prev_candle, 'open', 1)
        prev_close = _candle_get(prev_candle, 'close', 4)
        prev_volume = _candle_get(prev_candle, 'volume', 5)
        if prev_volume <= 0:
            return None, 0, 'bad_previous_volume', False

        current_side = _candle_direction(float(open_curr), float(current_price))
        prev_side = _candle_direction(prev_open, prev_close)
        if not current_side:
            return None, 0, 'current_flat_no_direction', False
        if not prev_side:
            return None, 0, 'previous_flat_no_direction', False

        current_ok, current_info = _is_tradeable_candle(open_curr, current_price, high_curr, low_curr)
        if not current_ok:
            return None, 0, f'current_candle_not_tradeable {current_info}', False

        prev_ok, prev_info = _is_tradeable_candle(prev_open, prev_close, _candle_get(prev_candle, 'high', 2), _candle_get(prev_candle, 'low', 3))
        if not prev_ok:
            return None, 0, f'previous_candle_not_tradeable {prev_info}', False

        flat_zone, flat_info = _is_flat_zone(recent_1m_history or [], current_price=current_price)
        if flat_zone:
            return None, 0, f'flat_zone_block {flat_info}', False

        current_speed = float(volume_curr) / max(elapsed, 0.001)
        previous_speed = float(prev_volume) / max(compare_tf, 0.001)
        # Lưu ý quan trọng:
        # Không so raw volume giữa nến hiện tại và nến so sánh, vì current_tf có thể là 1m
        # còn compare_tf có thể là 15m/1h. Tất cả phải quy đổi về tốc độ volume/giây.
        # Giữ tên key volume_reach_factor để không vỡ menu/config cũ, nhưng ý nghĩa là
        # current_speed phải đạt tối thiểu X lần previous_speed.
        speed_reach_factor = float(cfg.get('volume_reach_factor', 0.50))
        speed_up_factor = float(cfg.get('speed_up_factor', 1.00))
        speed_down_factor = float(cfg.get('speed_down_factor', 1.00))

        speed_reached = current_speed >= previous_speed * speed_reach_factor
        speed_up = current_speed > previous_speed * speed_up_factor and speed_reached
        speed_down_raw = current_speed < previous_speed * speed_down_factor
        # Nhanh hơn: xét realtime sau min_elapsed. Chậm hơn: chỉ xác nhận khi nến hiện tại đã đóng.
        speed_down = bool(current_is_final) and speed_down_raw

        signal = None
        case = None
        if current_side == prev_side:
            if speed_up:
                signal = current_side
                case = 'SAME_SIDE_SPEED_UP_FOLLOW_CURRENT'
            elif speed_down:
                signal = _opposite_side(current_side)
                case = 'SAME_SIDE_SPEED_DOWN_REVERSE'
        else:
            if speed_up:
                signal = current_side
                case = 'OPPOSITE_SIDE_CURRENT_FASTER_FOLLOW_CURRENT'

        if signal is None:
            return None, 0, (
                f'no_speed_case current_side={current_side} prev_side={prev_side} '
                f'volume_current={float(volume_curr):.4f} volume_prev={prev_volume:.4f} speed_reached={speed_reached} '
                f'cur_speed={current_speed:.8f} prev_speed={previous_speed:.8f} current_final={bool(current_is_final)} raw_slow={speed_down_raw}'
            ), False

        # Đảo ngược tín hiệu theo yêu cầu:
        # Tất cả điều kiện tốc độ vẫn giữ nguyên, chỉ đảo hướng cuối cùng trước khi vào/đảo lệnh.
        raw_signal = signal
        signal = _opposite_side(raw_signal)
        case = f'{case}_INVERTED'

        reason = (
            f'speed_2tf_ok | case={case} current_tf={current_interval} compare_tf={compare_interval} '
            f'elapsed={elapsed:.1f}s progress={progress:.3f} '
            f'volume_current={float(volume_curr):.4f} volume_prev={prev_volume:.4f} speed_reached={speed_reached} '
            f'current_speed={current_speed:.8f} prev_speed={previous_speed:.8f} current_final={bool(current_is_final)} '
            f'current_side={current_side} prev_side={prev_side} raw_signal={raw_signal} final_signal={signal}'
        )
        return signal, 1, reason, False
    except Exception as e:
        logger.error(f"Lỗi chấm điểm tín hiệu speed 2tf: {e}")
        return None, 0, 'error', False

def _kline_to_candle_dict(arr, symbol, interval, is_final=True):
    return {
        'symbol': symbol.upper(), 'interval': _normalize_interval(interval),
        'open': float(arr[1]), 'high': float(arr[2]), 'low': float(arr[3]),
        'close': float(arr[4]), 'volume': float(arr[5]),
        'is_final': is_final, 'time': int(arr[0]), 'close_time': int(arr[6]),
        'update_ts': time.time()
    }

def _fetch_rest_1m15m_signal_data(symbol):
    """Tên cũ giữ để tương thích: lấy nến hiện tại theo current_interval và nến đã đóng theo compare_interval."""
    try:
        cfg = _STRATEGY_CONFIG.get_all()
        current_interval = _normalize_interval(cfg.get('current_interval', cfg.get('signal_interval', '1m')))
        compare_interval = _normalize_interval(cfg.get('compare_interval', current_interval))
        symbol = symbol.upper()
        now = time.time()
        key = (symbol, current_interval, compare_interval)
        cached = _SIGNAL_DATA_CACHE.get(key)
        if cached and now - cached.get('ts', 0) < _SIGNAL_DATA_CACHE_TTL:
            return cached['data']

        url = "https://fapi.binance.com/fapi/v1/klines"
        curr_data = binance_api_request(url, params={"symbol": symbol, "interval": current_interval, "limit": 2})
        if not curr_data or len(curr_data) < 2:
            return None, None, None, []
        curr = curr_data[-1]  # nến hiện tại đang chạy theo current_interval

        if compare_interval == current_interval:
            prev = curr_data[-2]  # nến đóng gần nhất cùng khung
        else:
            cmp_data = binance_api_request(url, params={"symbol": symbol, "interval": compare_interval, "limit": 2})
            if not cmp_data or len(cmp_data) < 2:
                return None, None, None, []
            prev = cmp_data[-2]  # nến đã đóng gần nhất theo khung so sánh

        lookback = max(int(_STRATEGY_CONFIG.get('flat_zone_lookback', 5)) + 2, 7)
        if len(curr_data) < lookback + 1:
            hist_data = binance_api_request(url, params={"symbol": symbol, "interval": current_interval, "limit": lookback + 1})
        else:
            hist_data = curr_data
        closed_history = list(hist_data[:-1])[-lookback:] if hist_data else []
        result = (curr, prev, None, closed_history)
        _cleanup_signal_data_cache()
        _SIGNAL_DATA_CACHE[key] = {'ts': now, 'data': result}
        return result
    except Exception as e:
        logger.error(f"Lỗi REST lấy dữ liệu speed 2tf {symbol}: {e}")
        return None, None, None, []

def compute_signal_from_candles(prev_candle, curr_candle, prev15m_candle=None, recent_1m_history=None):
    try:
        open_curr = float(curr_candle[1]) if not isinstance(curr_candle, dict) else float(curr_candle['open'])
        high_curr = float(curr_candle[2]) if not isinstance(curr_candle, dict) else float(curr_candle['high'])
        low_curr = float(curr_candle[3]) if not isinstance(curr_candle, dict) else float(curr_candle['low'])
        close_curr = float(curr_candle[4]) if not isinstance(curr_candle, dict) else float(curr_candle['close'])
        volume_curr = float(curr_candle[5]) if not isinstance(curr_candle, dict) else float(curr_candle['volume'])
        progress = _safe_progress(curr_candle, _interval_seconds(_STRATEGY_CONFIG.get('signal_interval', '1m')))
        signal, score, reason, _ = _score_signal_parts(
            open_curr, close_curr, high_curr, low_curr, volume_curr,
            prev_candle, prev15m_candle, progress=progress, mode='entry', recent_1m_history=recent_1m_history,
            market_history=recent_1m_history, current_is_final=(progress >= 0.999)
        )
        return signal
    except Exception as e:
        logger.error(f"Lỗi tính tín hiệu từ nến speed-only: {e}")
        return None

def get_candle_signal_1h(symbol):
    """Tên cũ để tương thích: thực tế dùng speed-only theo khung nến đã chọn."""
    try:
        curr, prev1, prev15, history = _fetch_rest_1m15m_signal_data(symbol)
        if not curr or not prev1:
            return None
        return compute_signal_from_candles(prev1, curr, prev15, history)
    except Exception as e:
        logger.error(f"Lỗi phân tích tín hiệu speed-only {symbol}: {e}")
        return None

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

_POSITION_CACHE = {}
_POSITION_CACHE_LOCK = threading.RLock()
_POSITION_CACHE_TTL = 8.0

def get_position_cached(symbol, api_key, api_secret, ttl=_POSITION_CACHE_TTL, force=False):
    symbol = symbol.upper()
    now = time.time()
    cache_key = (symbol, api_key[-6:] if api_key else '')
    with _POSITION_CACHE_LOCK:
        item = _POSITION_CACHE.get(cache_key)
        if item and not force and now - item.get('ts', 0) < ttl:
            return item.get('pos')

    positions = get_positions(symbol, api_key, api_secret)
    pos = positions[0] if positions else None
    with _POSITION_CACHE_LOCK:
        _POSITION_CACHE[cache_key] = {'ts': now, 'pos': pos}
    return pos

def invalidate_position_cache(symbol, api_key=None):
    symbol = symbol.upper()
    with _POSITION_CACHE_LOCK:
        for key in list(_POSITION_CACHE.keys()):
            if key[0] == symbol:
                _POSITION_CACHE.pop(key, None)

def has_open_position_cached(symbol, api_key, api_secret, ttl=_POSITION_CACHE_TTL, force=False):
    pos = get_position_cached(symbol, api_key, api_secret, ttl=ttl, force=force)
    if not pos:
        return False
    try:
        return abs(float(pos.get('positionAmt', 0))) > 0
    except Exception:
        return False

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
        self._bot_manager = None
        self.bot_leverage = 10

    def set_bot_manager(self, bot_manager):
        self._bot_manager = bot_manager

    def find_best_coin_with_balance(self, excluded_coins=None):
        """Tìm coin dựa trên tín hiệu nến real-time (dùng RealtimeKlineManager nếu có)"""
        try:
            now = time.time()
            if now - self.last_scan_time < self.scan_cooldown:
                return None
            self.last_scan_time = now

            coins = get_coins_with_info()
            if not coins:
                logger.warning("⚠️ Cache coin trống, không thể tìm coin.")
                return None

            random.shuffle(coins)
            for coin in coins:
                symbol = coin['symbol']
                if symbol in _SYMBOL_BLACKLIST:
                    continue
                if excluded_coins and symbol in excluded_coins:
                    continue
                if float(_STRATEGY_CONFIG.get('low_volume_filter_enabled', 1.0)) >= 0.5:
                    min_vol = float(_STRATEGY_CONFIG.get('min_24h_volume', 0.0))
                    if float(coin.get('volume', 0.0) or 0.0) < min_vol:
                        continue
                if self._bot_manager and self._bot_manager.bot_coordinator.is_temp_blacklisted(symbol):
                    continue
                if self._bot_manager and self._bot_manager.coin_manager.is_coin_active(symbol):
                    continue

                signal = None
                if self._bot_manager and hasattr(self._bot_manager, 'kline_manager'):
                    kline_mgr = self._bot_manager.kline_manager
                    candle = kline_mgr.get_candle(symbol)
                    prev_candle = None  # cần lưu prev? ta sẽ lấy từ cache riêng
                    signal = get_candle_signal_1h(symbol)
                else:
                    signal = get_candle_signal_1h(symbol)

                if signal is None:
                    continue

                logger.info(f"✅ Tìm thấy coin {symbol} với tín hiệu {signal} | volume24h: {coin.get('volume', 0):.2f}")
                return symbol

            return None

        except Exception as e:
            logger.error(f"❌ Lỗi tìm coin: {str(e)}")
            logger.error(traceback.format_exc())
            return None

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

class RealtimeKlineManager:
    def __init__(self):
        self.connections = {}
        self._lock = threading.RLock()
        self._stop_event = threading.Event()
        self.executor = ThreadPoolExecutor(max_workers=10)
        self.candle_data = {}
        self.prev_candle_data = {}
        self.callbacks = defaultdict(list)

    def _current_interval(self):
        return _normalize_interval(_STRATEGY_CONFIG.get('current_interval', _STRATEGY_CONFIG.get('signal_interval', '1m')))

    def add_symbol(self, symbol, callback):
        symbol = symbol.upper()
        with self._lock:
            interval = self._current_interval()
            conn = self.connections.get(symbol)
            if (not conn) or conn.get('interval') != interval:
                if conn:
                    self.remove_symbol(symbol)
                self._load_initial_candles(symbol)
                self._connect(symbol)
            if callback not in self.callbacks[symbol]:
                self.callbacks[symbol].append(callback)

    def _to_candle_dict(self, arr, symbol, is_final=True, interval=None):
        interval = interval or self._current_interval()
        return {
            'symbol': symbol, 'interval': interval,
            'open': float(arr[1]), 'high': float(arr[2]), 'low': float(arr[3]),
            'close': float(arr[4]), 'volume': float(arr[5]),
            'is_final': is_final, 'time': int(arr[0]), 'close_time': int(arr[6]),
            'update_ts': time.time()
        }

    def _load_initial_candles(self, symbol):
        try:
            interval = self._current_interval()
            url = "https://fapi.binance.com/fapi/v1/klines"
            data = binance_api_request(url, params={"symbol": symbol.upper(), "interval": interval, "limit": 2})
            if data and len(data) >= 2:
                self.candle_data[symbol] = self._to_candle_dict(data[-1], symbol, is_final=False, interval=interval)
                self.prev_candle_data[symbol] = self._to_candle_dict(data[-2], symbol, is_final=True, interval=interval)
        except Exception as e:
            logger.error(f"Lỗi nạp nến ban đầu speed-only {symbol}: {e}")

    def _connect(self, symbol):
        interval = self._current_interval()
        stream = f"{symbol.lower()}@kline_{interval}"
        url = f"wss://fstream.binance.com/ws/{stream}"

        def on_message(ws, message):
            try:
                data = json.loads(message)
                k = data['k']
                if k['i'] != interval:
                    return
                candle = {
                    'symbol': symbol, 'interval': interval,
                    'open': float(k['o']), 'high': float(k['h']), 'low': float(k['l']),
                    'close': float(k['c']), 'volume': float(k['v']),
                    'is_final': k['x'], 'time': k['t'], 'close_time': k['T'],
                    'update_ts': time.time()
                }
                if candle['is_final']:
                    old_prev = self.prev_candle_data.get(symbol)
                    candle['prev_for_signal'] = old_prev.copy() if old_prev else None
                    self.candle_data.pop(symbol, None)
                else:
                    self.candle_data[symbol] = candle

                for cb in self.callbacks.get(symbol, []):
                    self.executor.submit(cb, symbol, candle)

                if candle['is_final']:
                    self.prev_candle_data[symbol] = candle.copy()
            except Exception as e:
                logger.error(f"Lỗi kline {interval} WS {symbol}: {e}")

        def on_error(ws, error):
            logger.error(f"Kline {interval} WS error {symbol}: {error}")
            if not self._stop_event.is_set() and symbol in self.connections:
                time.sleep(5)
                self._reconnect(symbol)

        def on_close(ws, close_status_code, close_msg):
            logger.info(f"Kline {interval} WS closed {symbol}")
            if not self._stop_event.is_set() and symbol in self.connections:
                time.sleep(5)
                self._reconnect(symbol)

        ws = websocket.WebSocketApp(url, on_message=on_message, on_error=on_error, on_close=on_close)
        thread = threading.Thread(target=ws.run_forever, daemon=True, name=f"kline-{interval}-{symbol}")
        thread.start()
        self.connections[symbol] = {'ws': ws, 'thread': thread, 'interval': interval}
        logger.info(f"🔗 Kline WebSocket {interval} cho {symbol}")

    def _reconnect(self, symbol):
        self.remove_symbol(symbol)
        self._load_initial_candles(symbol)
        self._connect(symbol)

    def remove_symbol(self, symbol):
        symbol = symbol.upper()
        with self._lock:
            conn = self.connections.pop(symbol, None)
            self.callbacks.pop(symbol, None)
            self.candle_data.pop(symbol, None)
            self.prev_candle_data.pop(symbol, None)
        if conn:
            try:
                conn['ws'].close()
            except Exception:
                pass

    def get_candle(self, symbol):
        return self.candle_data.get(symbol.upper())

    def get_prev_candle(self, symbol):
        return self.prev_candle_data.get(symbol.upper())

    def get_prev2_candle(self, symbol):
        return None

    def get_prev15_candle(self, symbol):
        return None

    def get_recent_1m_history(self, symbol):
        return []

    def stop(self):
        self._stop_event.set()
        for sym in list(self.connections.keys()):
            self.remove_symbol(sym)
        self.executor.shutdown(wait=False)

class BaseBot:
    def __init__(self, symbol, lev, percent, tp, sl, ws_manager, api_key, api_secret,
                 telegram_bot_token, telegram_chat_id, strategy_name, config_key=None, bot_id=None,
                 coin_manager=None, symbol_locks=None, max_coins=1, bot_coordinator=None,
                 kline_manager=None,   # Thêm kline manager
                 **kwargs):

        self.max_coins = 1
        self.active_symbols = []
        self.symbol_data = {}
        self.symbol = symbol.upper() if symbol else None

        self.lev = lev
        self.percent = percent
        self.tp = tp if tp else None
        self.sl = sl if sl else None
        self.ws_manager = ws_manager
        self.kline_manager = kline_manager
        self.api_key = api_key
        self.api_secret = api_secret
        self.telegram_bot_token = telegram_bot_token
        self.telegram_chat_id = telegram_chat_id
        self.strategy_name = strategy_name
        self.config_key = config_key
        self.bot_id = bot_id or f"{strategy_name}_{int(time.time())}_{random.randint(1000, 9999)}"

        self.status = "searching" if not symbol else "waiting"
        self._stop = False

        self.current_processing_symbol = None
        self.last_trade_completion_time = 0
        self.trade_cooldown = 30

        self.last_error_log_time = 0

        self.margin_safety_threshold = 1.05
        self.margin_safety_interval = 60
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

        self.enable_balance_orders = False
        self.balance_config = {}

        self.consecutive_failures = 0
        self.failure_cooldown_until = 0

        self.realtime_signal = {}        # symbol -> 'BUY'/'SELL'/None
        self.last_signal_time = {}       # symbol -> timestamp
        self.signal_cache_ttl = 2        # giây
        self.last_signal_debug_time = {}  # symbol -> timestamp, chống spam log debug tín hiệu
        self.exit_candidate = {}          # symbol -> {'side': ..., 'since': ...}

        self._pending_reverse = False
        self._reverse_symbol = None
        self._reverse_side = None

        if symbol:
            self._add_symbol(symbol)

        self.thread = threading.Thread(target=self._run, daemon=True, name=f"bot-{self.bot_id[-8:]}")
        self.thread.start()

        tp_sl_info = f" | TP: {self.tp}%" if self.tp else " | TP: Tắt"
        tp_sl_info += f" | SL: {self.sl}%" if self.sl else " | SL: Tắt"
        self.log(f"🟢 Bot {strategy_name} đã khởi động | 1 coin | Đòn bẩy: {lev}x | Vốn: {percent}% | Tín hiệu: speed 2 khung nến | Đảo chiều khi tín hiệu ngược đủ chuẩn{tp_sl_info}")

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

                if not self.active_symbols:
                    search_permission = self.bot_coordinator.request_coin_search(self.bot_id)

                    if search_permission:
                        if current_time - last_coin_search_log > log_interval:
                            queue_info = self.bot_coordinator.get_queue_info()
                            self.log(f"🔍 Đang tìm coin (vị trí: 1/{queue_info['queue_size'] + 1})...")
                            last_coin_search_log = current_time

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

                if self._pending_reverse:
                    self._pending_reverse = False
                    self._reverse_symbol = None
                    self._reverse_side = None

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

            if not symbol_info['position_open'] and current_time - symbol_info.get('added_time', current_time) > 300:
                self.log(f"⏰ {symbol} đã chờ vào lệnh quá 5 phút, dừng để tìm coin khác")
                self.stop_symbol(symbol, failed=True)
                return False

            if symbol_info['position_open']:
                self._check_symbol_tp_sl(symbol)
                self._check_realtime_exit(symbol)
                return False
            else:
                if self._pending_reverse and self._reverse_symbol == symbol:
                    return False

                if (current_time - symbol_info['last_trade_time'] > 30 and
                    current_time - symbol_info['last_close_time'] > 30):
                    signal = self._get_fresh_realtime_signal(symbol)
                    if signal is None:
                        return False

                    if self._open_symbol_position(symbol, signal, skip_signal_check=False):
                        symbol_info['last_trade_time'] = current_time
                        return True
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
            'margin_used': 0.0,
            'reverse_count': 0,
            'best_roi': None,
            'added_time': time.time()
        }
        self.ws_manager.add_symbol(symbol, lambda p, s=symbol: self._handle_price_update(s, p))
        if self.kline_manager:
            self.kline_manager.add_symbol(symbol, self._on_kline_update)
        self.coin_manager.register_coin(symbol)
        self.log(f"➕ Đã thêm {symbol} vào theo dõi")

    def _handle_price_update(self, symbol, price):
        if symbol not in self.symbol_data:
            return
        self.symbol_data[symbol]['last_price'] = price
        self.symbol_data[symbol]['last_price_time'] = time.time()

    def _on_kline_update(self, symbol, candle):
        """Callback từ kline manager.
        Chỉ cập nhật trạng thái tín hiệu mới nhất để xem/log.
        Quyết định đóng/đảo chiều vẫn được tính lại trực tiếp trong _check_realtime_exit().
        """
        if symbol not in self.symbol_data:
            return

        prev = candle.get('prev_for_signal') or (self.kline_manager.get_prev_candle(symbol) if self.kline_manager else None)
        _, _, _, history = _fetch_rest_1m15m_signal_data(symbol)
        if prev is None:
            self.realtime_signal[symbol] = None
            self.last_signal_time[symbol] = time.time()
            self.symbol_data[symbol]['realtime_signal'] = None
            return

        signal = self._compute_signal_from_candle(candle, prev, None, recent_1m_history=history)
        self.realtime_signal[symbol] = signal
        self.last_signal_time[symbol] = time.time()
        self.symbol_data[symbol]['realtime_signal'] = signal

    def _compute_signal_from_candle(self, current_candle, prev_candle, prev15_candle=None, mode='entry', return_details=False, recent_1m_history=None):
        """Tính tín hiệu speed-only theo khung nến đã chọn."""
        try:
            open_curr = float(current_candle['open'])
            current_price = float(current_candle.get('close', 0))
            symbol = current_candle.get('symbol')

            if symbol and symbol in self.symbol_data:
                last_price = float(self.symbol_data[symbol].get('last_price', 0) or 0)
                if last_price > 0:
                    current_price = last_price
                    current_candle['high'] = max(float(current_candle.get('high', current_price)), current_price)
                    current_candle['low'] = min(float(current_candle.get('low', current_price)), current_price)

            if current_price <= 0:
                details = {'signal': None, 'score': 0, 'reason': 'no_price', 'is_spike': False}
                return details if return_details else None

            progress = _safe_progress(current_candle, _interval_seconds(_STRATEGY_CONFIG.get('signal_interval', '1m')))
            signal, score, reason, is_spike = _score_signal_parts(
                open_curr, current_price, float(current_candle['high']), float(current_candle['low']), float(current_candle['volume']),
                prev_candle, prev15_candle, progress=progress, mode=mode, recent_1m_history=recent_1m_history,
                current_is_final=bool(current_candle.get('is_final', False)) or progress >= 0.999
            )
            details = {'signal': signal, 'score': score, 'reason': reason, 'is_spike': is_spike, 'progress': progress}
            return details if return_details else signal
        except Exception as e:
            logger.error(f"Lỗi compute signal speed-only: {e}")
            details = {'signal': None, 'score': 0, 'reason': 'error', 'is_spike': False}
            return details if return_details else None

    def _get_fresh_realtime_signal(self, symbol, mode='entry', return_details=False):
        """Tính tín hiệu mới ngay tại thời điểm kiểm tra bằng khung nến đã chọn."""
        try:
            symbol = symbol.upper()
            candle = None
            prev = None

            if self.kline_manager:
                candle = self.kline_manager.get_candle(symbol)
                prev = self.kline_manager.get_prev_candle(symbol)

            now = time.time()
            ws_stale = True
            if candle and not candle.get('is_final', False):
                update_ts = float(candle.get('update_ts', 0) or 0)
                ws_stale = update_ts <= 0 or (now - update_ts) > 3

            if (not candle) or (not prev) or ws_stale:
                rest_candle, rest_prev, rest_market, _ = self._get_rest_current_and_prev_candle(symbol)
                if rest_candle and rest_prev:
                    candle, prev = rest_candle, rest_prev
                    if self.kline_manager:
                        self.kline_manager.candle_data[symbol] = rest_candle
                        self.kline_manager.prev_candle_data[symbol] = rest_prev

            # Nếu khung so sánh khác khung hiện tại, prev của websocket không đúng khung.
            # Lấy nến đã đóng gần nhất của compare_interval qua REST/cache nhưng vẫn giữ candle realtime hiện tại nếu có.
            cfg = _STRATEGY_CONFIG.get_all()
            current_interval = _normalize_interval(cfg.get('current_interval', cfg.get('signal_interval', '1m')))
            compare_interval = _normalize_interval(cfg.get('compare_interval', current_interval))
            if compare_interval != current_interval:
                rest_curr_raw, rest_prev_raw, _, _ = _fetch_rest_1m15m_signal_data(symbol)
                if rest_prev_raw:
                    prev = rest_prev_raw
                if not candle and rest_curr_raw:
                    candle = {
                        'symbol': symbol.upper(), 'interval': current_interval,
                        'open': float(rest_curr_raw[1]), 'high': float(rest_curr_raw[2]), 'low': float(rest_curr_raw[3]),
                        'close': float(rest_curr_raw[4]), 'volume': float(rest_curr_raw[5]),
                        'is_final': False, 'time': int(rest_curr_raw[0]), 'close_time': int(rest_curr_raw[6]),
                        'update_ts': time.time()
                    }

            if not candle or not prev:
                details = {'signal': None, 'score': 0, 'reason': 'missing_candles', 'is_spike': False}
                self.realtime_signal[symbol] = None
                self.last_signal_time[symbol] = time.time()
                if symbol in self.symbol_data:
                    self.symbol_data[symbol]['realtime_signal'] = None
                return details if return_details else None

            _, _, _, closed_history = _fetch_rest_1m15m_signal_data(symbol)
            details = self._compute_signal_from_candle(candle, prev, None, mode=mode, return_details=True, recent_1m_history=closed_history)
            signal = details.get('signal')

            self.realtime_signal[symbol] = signal
            self.last_signal_time[symbol] = time.time()
            if symbol in self.symbol_data:
                self.symbol_data[symbol]['realtime_signal'] = signal
                self.symbol_data[symbol]['last_signal_details'] = details

            return details if return_details else signal
        except Exception as e:
            logger.error(f"Lỗi lấy tín hiệu realtime mới nhất {symbol}: {e}")
            details = {'signal': None, 'score': 0, 'reason': 'error', 'is_spike': False}
            return details if return_details else None

    def _get_rest_current_and_prev_candle(self, symbol):
        """REST fallback: current + previous của khung signal_interval."""
        try:
            curr, prev, market, market_history = _fetch_rest_1m15m_signal_data(symbol)
            if not curr or not prev:
                return None, None, None, []
            interval = _normalize_interval(_STRATEGY_CONFIG.get('current_interval', _STRATEGY_CONFIG.get('signal_interval', '1m')))
            market_interval = _normalize_interval(_STRATEGY_CONFIG.get('compare_interval', interval))
            def conv(arr, is_final, used_interval):
                return {
                    'symbol': symbol.upper(), 'interval': used_interval,
                    'open': float(arr[1]), 'high': float(arr[2]), 'low': float(arr[3]),
                    'close': float(arr[4]), 'volume': float(arr[5]),
                    'is_final': is_final, 'time': int(arr[0]), 'close_time': int(arr[6]),
                    'update_ts': time.time()
                }
            market_candle = conv(market, False, market_interval) if market else None
            if market_candle is not None:
                market_candle['history'] = market_history
            return conv(curr, False, interval), conv(prev, True, interval), market_candle, market_history
        except Exception as e:
            logger.error(f"Lỗi REST fallback lấy nến speed-only {symbol}: {e}")
            return None, None, None, []

    def _debug_realtime_signal(self, symbol, current_side=None):
        """Log nhanh lý do chưa có tín hiệu để kiểm tra volume/body thực tế bot đang thấy."""
        try:
            now = time.time()
            if now - self.last_signal_debug_time.get(symbol, 0) < 5:
                return
            self.last_signal_debug_time[symbol] = now

            candle = self.kline_manager.get_candle(symbol) if self.kline_manager else None
            prev = self.kline_manager.get_prev_candle(symbol) if self.kline_manager else None
            if not candle or not prev:
                self.log(f"🔎 {symbol} chưa đủ dữ liệu kline để xét đảo chiều | candle={bool(candle)} prev={bool(prev)} side={current_side}")
                return

            open_curr = float(candle['open'])
            price = float(self.symbol_data.get(symbol, {}).get('last_price', 0) or candle.get('close', 0) or 0)
            body_curr = abs(price - open_curr)
            body_prev = abs(float(prev['close']) - float(prev['open']))
            vol_curr = float(candle['volume'])
            vol_prev = float(prev['volume'])
            direction = 'BUY' if price > open_curr else 'SELL' if price < open_curr else 'FLAT'
        except Exception as e:
            logger.error(f"Lỗi debug signal {symbol}: {e}")

    def _check_realtime_exit(self, symbol):
        """
        Đóng/đảo chiều ngay khi xuất hiện tín hiệu ngược đủ chuẩn.
        Tín hiệu đóng và mở dùng chung một bộ chấm điểm để tránh trường hợp mở nhạy nhưng đóng quá trễ.
        """
        if symbol not in self.symbol_data:
            return

        data = self.symbol_data[symbol]
        if not data['position_open']:
            return

        current_side = data.get('side')
        if current_side not in ('BUY', 'SELL'):
            return

        details = self._get_fresh_realtime_signal(symbol, mode='entry', return_details=True)
        signal = details.get('signal')

        self._debug_realtime_signal(symbol, current_side)

        if signal is None or signal == current_side:
            return

        self.log(
            f"🕯️ {symbol} - Tín hiệu realtime ngược đủ chuẩn ({signal} vs {current_side}) | "
            f"score={details.get('score')} | {details.get('reason')} | đóng lệnh và đảo chiều ngay"
        )
        self._close_symbol_position(symbol, reason="Candle opposite (same realtime signal)", reverse_side=signal)
        return

    def _check_symbol_tp_sl(self, symbol):
        if symbol not in self.symbol_data:
            return
        data = self.symbol_data[symbol]
        if not data['position_open']:
            return

        entry = float(data.get('entry', 0) or 0)
        if entry <= 0 or abs(float(data.get('qty', 0) or 0)) <= 0:
            return

        current_price = self.get_current_price(symbol)
        if current_price <= 0:
            return

        if data['side'] == 'BUY':
            roi = (current_price - entry) / entry * 100 * self.lev
        else:
            roi = (entry - current_price) / entry * 100 * self.lev

        if float(_STRATEGY_CONFIG.get('profit_protect_enabled', 1.0)) >= 0.5:
            best_roi = data.get('best_roi')
            if best_roi is None:
                best_roi = roi
            best_roi = max(float(best_roi), float(roi))
            data['best_roi'] = best_roi
            start_roi = float(_STRATEGY_CONFIG.get('profit_protect_start_roi', 10.0))
            pullback_roi = float(_STRATEGY_CONFIG.get('profit_protect_pullback_roi', 8.0))
            if best_roi >= start_roi and (best_roi - roi) >= pullback_roi:
                self.log(f"🔒 {symbol} - Hút lực từ đỉnh: ROI đỉnh {best_roi:.2f}% tụt còn {roi:.2f}%, đóng lệnh bảo vệ lời")
                self._close_symbol_position(symbol, reason="Profit protect peak pullback")
                return

        if self.tp and roi >= self.tp:
            self.log(f"🎯 {symbol} - Đạt TP {self.tp}%, đóng lệnh")
            self._close_symbol_position(symbol, reason=f"TP {self.tp}%")
            return
        if self.sl and roi <= -self.sl:
            self.log(f"🛡️ {symbol} - Đạt SL {self.sl}%, đóng lệnh")
            self._close_symbol_position(symbol, reason=f"SL {self.sl}%")
            return

    def _close_symbol_position(self, symbol, reason="", reverse_side=None):
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
                prev_margin_used = float(self.symbol_data[symbol].get('margin_used', 0.0) or 0.0)
                prev_reverse_count = int(self.symbol_data[symbol].get('reverse_count', 0) or 0)
                if prev_margin_used <= 0:
                    try:
                        prev_margin_used = (qty * self._get_fresh_price(symbol)) / max(float(self.lev), 1.0)
                    except Exception:
                        prev_margin_used = 0.0
                close_side = "SELL" if side == "BUY" else "BUY"

                cancel_all_orders(symbol, self.api_key, self.api_secret)
                time.sleep(1)

                result = place_order(symbol, close_side, qty, self.api_key, self.api_secret)
                invalidate_position_cache(symbol, self.api_key)
                if result and 'orderId' in result:
                    self.log(f"🔴 Đã đóng vị thế {symbol} | Lý do: {reason}")
                    time.sleep(1)
                    self._reset_symbol_position(symbol)

                    if "Candle opposite" in reason:
                        reverse_side = reverse_side or ("SELL" if side == "BUY" else "BUY")
                        self._pending_reverse = False
                        self._reverse_symbol = None
                        self._reverse_side = None
                        self.log(f"🔄 Đảo chiều ngay {symbol} sang {reverse_side}")
                        if prev_reverse_count >= int(_STRATEGY_CONFIG.get('max_reverse_count', 2)):
                            self.log(f"⛔ {symbol} đã đảo {prev_reverse_count} lần liên tiếp, dừng coin để tránh sideway")
                            self.stop_symbol(symbol, failed=True)
                            return True
                        if self._open_symbol_position(symbol, reverse_side, skip_signal_check=True, margin_override=None, is_reverse=True, reverse_count=prev_reverse_count + 1):
                            self.log(f"✅ Đảo chiều thành công trên {symbol}")
                        else:
                            self.log(f"❌ Đảo chiều thất bại trên {symbol}, dừng coin")
                            self.stop_symbol(symbol, failed=True)
                    elif "TP" in reason or "SL" in reason:
                        self.log(f"⛔ {symbol} đóng do TP/SL với cả hai ngưỡng, sẽ tìm coin mới")
                        self._blacklist_and_stop_symbol(symbol, reason=reason)
                    else:
                        self._blacklist_and_stop_symbol(symbol, reason=reason)

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

    def _open_symbol_position(self, symbol, side, skip_signal_check=False, margin_override=None, is_reverse=False, reverse_count=0):
        with self.symbol_locks[symbol]:
            try:
                if self.symbol_data.get(symbol, {}).get('position_open'):
                    self.log(f"⚠️ {symbol} local đang có vị thế, không mở thêm")
                    return False

                if not skip_signal_check:
                    current_signal = self._get_fresh_realtime_signal(symbol)
                    if current_signal is None or current_signal != side:
                        self.log(f"⚠️ {symbol} tín hiệu realtime không còn phù hợp ({current_signal} vs {side})")
                        self.stop_symbol(symbol, failed=True)
                        return False

                if not set_leverage(symbol, self.lev, self.api_key, self.api_secret):
                    self.log(f"❌ {symbol} - Không thể cài đặt đòn bẩy {self.lev}x")
                    self.stop_symbol(symbol, failed=True)
                    return False

                total_balance, available_balance = get_total_and_available_balance(self.api_key, self.api_secret)
                margin_balance = get_margin_balance(self.api_key, self.api_secret)
                if margin_balance is None or margin_balance <= 0:
                    self.log(f"❌ {symbol} - Không thể lấy số dư margin")
                    self.stop_symbol(symbol, failed=True)
                    return False

                required_usd = margin_balance * (self.percent / 100)
                sizing_label = f"{self.percent}% số dư margin hiện tại"

                if required_usd <= 0:
                    self.log(f"❌ {symbol} - Vốn vào lệnh quá nhỏ ({required_usd:.2f})")
                    self.stop_symbol(symbol, failed=True)
                    return False

                if available_balance is not None and required_usd > available_balance:
                    self.log(f"⚠️ {symbol} - Vốn tính theo margin ({required_usd:.2f}) > số dư khả dụng ({available_balance:.2f}), vẫn thử lệnh theo yêu cầu margin...")

                current_price = self._get_fresh_price(symbol)
                if current_price <= 0:
                    self.log(f"❌ {symbol} - Lỗi giá")
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
                invalidate_position_cache(symbol, self.api_key)
                if result and 'orderId' in result:
                    executed_qty = float(result.get('executedQty') or result.get('origQty') or qty)
                    avg_price = float(result.get('avgPrice') or current_price)
                    if executed_qty <= 0:
                        executed_qty = qty
                    if avg_price <= 0:
                        avg_price = current_price

                    self.symbol_data[symbol].update({
                        'entry': avg_price,
                        'entry_base': avg_price,
                        'qty': executed_qty if side == "BUY" else -executed_qty,
                        'side': side,
                        'position_open': True,
                        'status': "open",
                        'last_trade_time': time.time(),
                        'margin_used': required_usd,
                        'reverse_count': int(reverse_count) if is_reverse else 0,
                        'best_roi': 0.0,
                    })

                    self.bot_coordinator.bot_has_coin(self.bot_id)
                    if hasattr(self, '_bot_manager') and self._bot_manager:
                        self._bot_manager.bot_coordinator.release_coin(symbol)

                    self.consecutive_failures = 0
                    message = (f"✅ <b>ĐÃ MỞ VỊ THẾ {symbol}</b>\n"
                               f"🤖 Bot: {self.bot_id}\n📌 Hướng: {side}\n"
                               f"🏷️ Entry: {self.symbol_data[symbol]['entry']:.4f}\n"
                               f"📊 Khối lượng: {abs(self.symbol_data[symbol]['qty']):.4f}\n"
                               f"💵 Vốn vào lệnh: {required_usd:.2f} USDT ({sizing_label})\n"
                               f"💰 Đòn bẩy: {self.lev}x\n")
                    if self.tp: message += f"🎯 TP: {self.tp}% | "
                    if self.sl: message += f"🛡️ SL: {self.sl}%"
                    message += f"\n🔄 Thoát: Tín hiệu ngược đủ chuẩn thì đảo ngay; có hút lực từ đỉnh hoặc TP/SL"
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
            pos = get_position_cached(symbol, self.api_key, self.api_secret, ttl=8.0, force=True)
            if pos:
                amt = float(pos.get('positionAmt', 0))
                if abs(amt) > 0:
                    return pos
            return None
        except Exception as e:
            logger.error(f"Lỗi force check position {symbol}: {str(e)}")
            return None

    def _check_symbol_position(self, symbol):
        """Kiểm tra vị thế thủ công/có cooldown. Không gọi lặp 2 lần để tránh spam API."""
        try:
            pos = get_position_cached(symbol, self.api_key, self.api_secret, ttl=15.0, force=False)
            if pos:
                amt = float(pos.get('positionAmt', 0))
                if abs(amt) > 0:
                    if not self.symbol_data[symbol]['position_open']:
                        entry_price = float(pos.get('entryPrice', 0))
                        if entry_price == 0:
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
                'margin_used': 0.0,
                'best_roi': None,
            })
            self.symbol_data[symbol]['last_close_time'] = time.time()

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

        if self.kline_manager:
            try:
                self.kline_manager.remove_symbol(symbol)
            except Exception as e:
                self.log(f"❌ Lỗi dừng Kline WS {symbol}: {str(e)}")

        try:
            self.active_symbols.remove(symbol)
        except ValueError:
            self.log(f"⚠️ {symbol} không có trong active_symbols khi dừng")

        self.coin_manager.unregister_coin(symbol)
        self.realtime_signal.pop(symbol, None)
        self.last_signal_time.pop(symbol, None)

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

class BotManager:
    def __init__(self, api_key=None, api_secret=None, telegram_bot_token=None, telegram_chat_id=None):
        self.ws_manager = WebSocketManager()
        self.kline_manager = RealtimeKlineManager()   # Thêm kline manager
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

        if api_key and api_secret:
            self._verify_api_connection()
            self.log("🟢 HỆ THỐNG BOT TÍN HIỆU 2 NẾN 1h REAL-TIME (VOLUME+BODY) - ĐẢO CHIỀU KHI TÍN HIỆU NGƯỢC")
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
                    'tp': bot.tp,
                    'sl': bot.sl,
                })

            summary = "📊 **THỐNG KÊ CHI TIẾT - BOT TÍN HIỆU 2 NẾN 1h REAL-TIME (VOLUME+BODY)**\n\n"

            cache_stats = _COINS_CACHE.get_stats()
            coins_in_cache = cache_stats['count']
            last_price_update = cache_stats['last_price_update']
            update_time = time.ctime(last_price_update) if last_price_update > 0 else "Chưa cập nhật"

            summary += f"🗂️ **CACHE HỆ THỐNG**: {coins_in_cache} coin | Cập nhật: {update_time}\n"
            summary += get_strategy_config_text().replace("<b>", "**").replace("</b>", "**") + "\n\n"

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
                    tp_sl_str = f"TP:{bot['tp']}%" if bot['tp'] else "TP:Tắt"
                    tp_sl_str += f" SL:{bot['sl']}%" if bot['sl'] else " SL:Tắt"
                    summary += f"{status_emoji} **bot_{bot['index']}** {tp_sl_str}\n"
                    summary += f"   💰 Đòn bẩy: {bot['leverage']}x | Vốn: {bot['percent']}%\n"
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
            "🤖 <b>BOT GIAO DỊCH FUTURES - TÍN HIỆU 2 NẾN 1h REAL-TIME (VOLUME + BODY)</b>\n\n"
            "🎯 <b>CƠ CHẾ HOẠT ĐỘNG:</b>\n"
            "• Tín hiệu được tính liên tục dựa trên nến 1h đang hình thành (thân nến = giá hiện tại - giá mở, volume lũy kế).\n"
            "• Khi tín hiệu ngược hướng với vị thế → đóng lệnh và ĐẢO CHIỀU ngay trên cùng coin.\n"
            "• Nếu đặt cả TP và SL, khi chạm TP hoặc SL sẽ đóng và chuyển sang coin khác.\n"
            "• Không sử dụng cân bằng/lọc coin, không nhồi lệnh.\n"
            "• Vào lệnh bằng điểm lực nến realtime; đóng/đảo chiều chỉ khi tín hiệu ngược đủ mạnh và duy trì đủ thời gian.\n\n"
            "📌 <b>LƯU Ý:</b> Có thể chỉnh tham số chiến lược từ nút 🎯 Chiến lược."
        )
        send_telegram(welcome, chat_id=chat_id, reply_markup=create_main_menu(),
                     bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

    def add_bot(self, symbol, lev, percent, tp, sl, strategy_type, bot_count=1, **kwargs):
        if sl == 0: sl = None
        if tp == 0: tp = None

        if not self.api_key or not self.api_secret:
            self.log("❌ API Key chưa được cài đặt trong BotManager")
            return False

        if not self._verify_api_connection():
            self.log("❌ KHÔNG THỂ KẾT NỐI VỚI BINANCE - KHÔNG THỂ TẠO BOT")
            return False

        bot_mode = kwargs.get('bot_mode', 'static')

        created_count = 0
        for i in range(bot_count):
            if bot_mode == 'static' and symbol:
                bot_id = f"STATIC_{strategy_type}_{int(time.time())}_{i}"
            else:
                bot_id = f"DYNAMIC_{strategy_type}_{int(time.time())}_{i}"
            if bot_id in self.bots:
                continue

            bot = BaseBot(
                symbol, lev, percent, tp, sl, self.ws_manager,
                self.api_key, self.api_secret, self.telegram_bot_token, self.telegram_chat_id,
                coin_manager=self.coin_manager, symbol_locks=self.symbol_locks,
                bot_coordinator=self.bot_coordinator, bot_id=bot_id, max_coins=1,
                strategy_name=strategy_type,
                kline_manager=self.kline_manager   # Truyền kline manager
            )
            bot._bot_manager = self
            bot.coin_finder.set_bot_manager(self)
            self.bots[bot_id] = bot
            created_count += 1

        if created_count > 0:
            tp_info = f"🎯 TP: {tp}%" if tp else "🎯 TP: Tắt"
            sl_info = f"🛡️ SL: {sl}%" if sl else "🛡️ SL: Tắt"
            success_msg = (f"✅ <b>ĐÃ TẠO {created_count} BOT TÍN HIỆU 2 NẾN 1h REAL-TIME (VOLUME+BODY)</b>\n\n"
                           f"🎯 Chiến lược: {strategy_type}\n💰 Đòn bẩy: {lev}x\n"
                           f"📈 % Số dư: {percent}%\n{tp_info}\n{sl_info}\n"
                           f"🔧 Chế độ: {bot_mode}\n🔢 Số bot: {created_count}\n")
            if bot_mode == 'static' and symbol:
                success_msg += f"🔗 Coin ban đầu: {symbol}\n"
            else:
                success_msg += f"🔗 Coin: Tự động tìm theo tín hiệu nến real-time (USDT/USDC)\n"
            success_msg += "🎯 Tham số chiến lược dùng theo cấu hình Telegram hiện tại.\n"
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

        strategy_key_map = {
            '✏️ Current timeframe': ('current_interval', 'Khung nến hiện tại để đo tốc độ realtime. Ví dụ: 1m, 3m, 5m, 15m.'),
            '✏️ Compare timeframe': ('compare_interval', 'Khung nến đã đóng gần nhất để so sánh tốc độ. Ví dụ: 1m, 15m, 1h.'),
            '✏️ Signal timeframe': ('current_interval', 'Tên cũ: khung nến hiện tại để đo tốc độ realtime.'),
            '✏️ Min elapsed seconds': ('min_elapsed_seconds', 'Số giây tối thiểu của nến hiện tại trước khi xét. Ví dụ 6, 10, 15.'),
            '✏️ Speed reach factor': ('volume_reach_factor', 'Tốc độ nến hiện tại phải đạt tối thiểu bao nhiêu lần tốc độ nến so sánh. Ví dụ 0.50.'),
            '✏️ Speed up factor': ('speed_up_factor', 'Current speed phải lớn hơn previous speed bao nhiêu lần để coi là tăng tốc. Ví dụ 1.0, 1.2.'),
            '✏️ Speed down factor': ('speed_down_factor', 'Current speed nhỏ hơn previous speed bao nhiêu lần để coi là giảm tốc. Lưu ý: giảm tốc chỉ xác nhận khi nến hiện tại đã đóng. Ví dụ 1.0, 0.8.'),
            '✏️ Min body ratio': ('body_ratio_min', 'Thân nến/range tối thiểu để tránh doji. Ví dụ 0.25.'),
            '✏️ Min range pct': ('min_range_pct', 'Range tối thiểu của nến theo % giá để tránh nến quá thấp. Ví dụ 0.08.'),
            '✏️ Min body pct': ('min_body_pct', 'Thân nến tối thiểu theo % giá. Ví dụ 0.03.'),
            '✏️ Flat zone lookback': ('flat_zone_lookback', 'Số nến đóng gần nhất để kiểm tra vùng bẹt. 0 hoặc 1 = tắt. Ví dụ 5.'),
            '✏️ Min box range pct': ('min_box_range_pct', 'Range tối thiểu của cụm nến theo % giá để tránh vùng bẹt. Ví dụ 0.15.'),
            '✏️ Low volume filter': ('low_volume_filter_enabled', '1 = bật lọc coin volume 24h thấp; 0 = tắt'),
            '✏️ Min 24h volume': ('min_24h_volume', 'Volume 24h tối thiểu của coin để bot động chọn. Ví dụ 10000000, 50000000'),
            '✏️ Profit protect ON/OFF': ('profit_protect_enabled', '1 = bật hút lực từ đỉnh, 0 = tắt.'),
            '✏️ Profit start ROI': ('profit_protect_start_roi', 'ROI tối thiểu để bắt đầu bảo vệ lợi nhuận. Ví dụ 10, 20, 30.'),
            '✏️ Profit pullback ROI': ('profit_protect_pullback_roi', 'Khi ROI tụt khỏi đỉnh bao nhiêu % thì đóng. Ví dụ 5, 8, 10.'),
        }

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
            send_telegram(self.get_position_summary(), chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "➕ Thêm Bot":
            self.user_states[chat_id] = {'step': 'waiting_bot_mode'}
            send_telegram("🤖 Chọn chế độ bot:", chat_id=chat_id, reply_markup=create_bot_mode_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⛔ Dừng Bot":
            if not self.bots:
                send_telegram("🤖 Không có bot nào để dừng.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
                keyboard = [[{"text": f"bot_{idx}"}] for idx, _ in enumerate(sorted_bots, start=1)]
                keyboard.append([{"text": "❌ Hủy bỏ"}])
                self.user_states[chat_id] = {'step': 'waiting_stop_bot'}
                send_telegram("⛔ Chọn bot muốn dừng:", chat_id=chat_id,
                             reply_markup={"keyboard": keyboard, "resize_keyboard": True, "one_time_keyboard": True},
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⛔ Quản lý Coin":
            kb = self.get_coin_management_keyboard()
            if not kb:
                send_telegram("📭 Chưa có coin nào đang được bot theo dõi.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                self.user_states[chat_id] = {'step': 'waiting_stop_coin'}
                send_telegram("⛔ Chọn coin muốn dừng:", chat_id=chat_id, reply_markup=kb,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "📈 Vị thế":
            positions = get_positions(api_key=self.api_key, api_secret=self.api_secret)
            open_positions = [p for p in positions if abs(float(p.get('positionAmt', 0))) > 0]
            if not open_positions:
                msg = "📭 Không có vị thế đang mở."
            else:
                msg = "📈 <b>VỊ THẾ ĐANG MỞ</b>\n\n"
                for p0 in open_positions[:20]:
                    qty = float(p0.get('positionAmt', 0))
                    side = "BUY" if qty > 0 else "SELL"
                    msg += f"• {p0.get('symbol')} | {side} | qty={abs(qty)} | PnL={float(p0.get('unRealizedProfit', 0)):.3f}\n"
            send_telegram(msg, chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "💰 Số dư":
            total, available = get_total_and_available_balance(self.api_key, self.api_secret)
            margin = get_margin_balance(self.api_key, self.api_secret)
            if total is not None:
                msg = (f"💰 <b>SỐ DƯ</b>\n\n"
                       f"• Tổng số dư: {total:.2f}\n"
                       f"• Khả dụng: {available:.2f}\n"
                       f"• Ký quỹ: {margin:.2f}")
            else:
                msg = "❌ Không thể lấy số dư"
            send_telegram(msg, chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⚙️ Cấu hình":
            send_telegram("⚙️ Cấu hình chính hiện nằm trong mục 🎯 Chiến lược.", chat_id=chat_id,
                         reply_markup=create_main_menu(), bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "🎯 Chiến lược":
            self.user_states[chat_id] = {'step': 'waiting_strategy_config'}
            send_telegram(get_strategy_config_text(), chat_id=chat_id, reply_markup=create_strategy_config_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "❌ Hủy bỏ":
            self.user_states[chat_id] = {}
            send_telegram("❌ Đã hủy thao tác.", chat_id=chat_id, reply_markup=create_main_menu(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_strategy_config':
            if text == '📊 Xem tham số chiến lược':
                send_telegram(get_strategy_config_text(), chat_id=chat_id, reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text in ('🔄 Reset chiến lược', '♻️ Reset tham số chiến lược'):
                _STRATEGY_CONFIG.reset()
                send_telegram("✅ Đã reset tham số chiến lược về mặc định.\n\n" + get_strategy_config_text(),
                             chat_id=chat_id, reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text in strategy_key_map:
                key, help_text = strategy_key_map[text]
                self.user_states[chat_id] = {'step': 'waiting_strategy_value', 'strategy_key': key}
                send_telegram(f"✏️ Nhập giá trị mới cho <b>{key}</b>\n{help_text}", chat_id=chat_id,
                             reply_markup=create_strategy_value_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("⚠️ Chọn tham số cần chỉnh.", chat_id=chat_id, reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_strategy_value':
            if text == "❌ Hủy bỏ":
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            try:
                key = user_state.get('strategy_key')
                if key in ('signal_interval', 'current_interval', 'compare_interval', 'market_interval'):
                    val = _normalize_interval(text)
                    if val != text.strip().lower():
                        raise ValueError
                    _STRATEGY_CONFIG.update(**{key: val})
                else:
                    val = float(text)
                    if key in ('entry_score', 'exit_score', 'breakout_lookback', 'max_reverse_count', 'flat_zone_lookback'):
                        val = int(val)
                        if val < 0 or val > 50:
                            raise ValueError
                    elif key == 'max_reverse_balance_percent':
                        if not (0 < val <= 100):
                            raise ValueError
                    elif val <= 0:
                        raise ValueError
                    _STRATEGY_CONFIG.update(**{key: val})
                self.user_states[chat_id] = {'step': 'waiting_strategy_config'}
                send_telegram("✅ Đã cập nhật.\n\n" + get_strategy_config_text(), chat_id=chat_id,
                             reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            except Exception:
                send_telegram("⚠️ Giá trị không hợp lệ. Hãy nhập số phù hợp.", chat_id=chat_id,
                             reply_markup=create_strategy_value_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_bot_mode':
            if text == "🤖 Bot Tĩnh - Coin cụ thể":
                user_state['bot_mode'] = 'static'
                user_state['step'] = 'waiting_symbol'
                send_telegram("🔗 Nhập tên coin, ví dụ SOLUSDT:", chat_id=chat_id, reply_markup=create_symbols_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text == "🔄 Bot Động - Tự tìm coin":
                user_state['bot_mode'] = 'dynamic'
                user_state['step'] = 'waiting_leverage'
                send_telegram("⚙️ Chọn đòn bẩy:", chat_id=chat_id, reply_markup=create_leverage_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("⚠️ Vui lòng chọn chế độ bot hợp lệ.", chat_id=chat_id, reply_markup=create_bot_mode_keyboard(),
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
            try:
                lev = int(text.replace('x', ''))
                if lev <= 0:
                    raise ValueError
                user_state['leverage'] = lev
                user_state['step'] = 'waiting_percent'
                send_telegram("📊 Chọn % số dư cho mỗi lệnh:", chat_id=chat_id, reply_markup=create_percent_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            except Exception:
                send_telegram("⚠️ Vui lòng nhập/chọn đòn bẩy hợp lệ.", chat_id=chat_id, reply_markup=create_leverage_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_percent':
            try:
                percent = float(text)
                if percent <= 0 or percent > 100:
                    raise ValueError
                user_state['percent'] = percent
                user_state['step'] = 'waiting_tp'
                send_telegram("🎯 Nhập TP % ROI sau đòn bẩy, hoặc bỏ qua:", chat_id=chat_id, reply_markup=create_tp_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            except Exception:
                send_telegram("⚠️ Vui lòng nhập % hợp lệ.", chat_id=chat_id, reply_markup=create_percent_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_tp':
            if text == "❌ Bỏ qua (không TP)":
                user_state['tp'] = None
            elif text != "❌ Hủy bỏ":
                try:
                    tp = float(text)
                    if tp < 0:
                        raise ValueError
                    user_state['tp'] = tp if tp > 0 else None
                except Exception:
                    send_telegram("⚠️ Vui lòng nhập TP >= 0.", chat_id=chat_id, reply_markup=create_tp_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    return
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            user_state['step'] = 'waiting_sl'
            send_telegram("🛡️ Nhập SL % ROI sau đòn bẩy, hoặc bỏ qua:", chat_id=chat_id, reply_markup=create_sl_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_sl':
            if text == "❌ Bỏ qua (không SL)":
                user_state['sl'] = None
            elif text != "❌ Hủy bỏ":
                try:
                    sl = float(text)
                    if sl < 0:
                        raise ValueError
                    user_state['sl'] = sl if sl > 0 else None
                except Exception:
                    send_telegram("⚠️ Vui lòng nhập SL >= 0.", chat_id=chat_id, reply_markup=create_sl_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    return
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return

            if user_state.get('bot_mode') == 'static':
                self._finish_bot_creation(chat_id, user_state)
            else:
                user_state['step'] = 'waiting_bot_count'
                send_telegram("🔢 Nhập số bot muốn tạo:", chat_id=chat_id, reply_markup=create_bot_count_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_bot_count':
            try:
                bot_count = int(text)
                if bot_count <= 0:
                    raise ValueError
                user_state['bot_count'] = bot_count
                self._finish_bot_creation(chat_id, user_state)
            except Exception:
                send_telegram("⚠️ Vui lòng nhập số nguyên > 0.", chat_id=chat_id, reply_markup=create_bot_count_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_stop_bot':
            if text.startswith("bot_"):
                try:
                    idx = int(text.split("_")[1])
                    sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
                    bot_id = sorted_bots[idx-1][0]
                    self.stop_bot(bot_id)
                    send_telegram(f"✅ Đã dừng {text}", chat_id=chat_id, reply_markup=create_main_menu(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                except Exception:
                    send_telegram("❌ Bot không tồn tại.", chat_id=chat_id, reply_markup=create_main_menu(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            self.user_states[chat_id] = {}

        elif current_step == 'waiting_stop_coin':
            if text.startswith("⛔ Coin: "):
                coin = text.replace("⛔ Coin: ", "")
                self.stop_coin(coin)
                send_telegram(f"✅ Đã dừng coin {coin}", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text == "⛔ DỪNG TẤT CẢ COIN":
                self.stop_all_coins()
                send_telegram("✅ Đã dừng tất cả coin", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            self.user_states[chat_id] = {}

        else:
            self.send_main_menu(chat_id)

    def _finish_bot_creation(self, chat_id, user_state):
        try:
            bot_mode = user_state.get('bot_mode', 'static')
            leverage = user_state.get('leverage')
            percent = user_state.get('percent')
            tp = user_state.get('tp')
            sl = user_state.get('sl')
            symbol = user_state.get('symbol')
            bot_count = user_state.get('bot_count', 1)

            success = self.add_bot(
                symbol=symbol, lev=leverage, percent=percent, tp=tp, sl=sl,
                strategy_type="SpeedPatternStrategy",
                bot_mode=bot_mode, bot_count=bot_count
            )

            if success:
                success_msg = (
                    f"✅ <b>ĐÃ TẠO BOT MARKET REGIME + SPEED THÀNH CÔNG</b>\n\n"
                    f"🤖 Chiến lược: speed pattern 5+1 + profit protect\n"
                    f"🔧 Chế độ: {bot_mode}\n"
                    f"🔢 Số bot: {bot_count}\n"
                    f"💰 Đòn bẩy: {leverage}x\n"
                    f"📊 % Số dư: {percent}%\n"
                    f"🎯 TP: {tp if tp else 'Tắt'}\n"
                    f"🛡️ SL: {sl if sl else 'Tắt'}\n"
                    f"🔄 Thoát: tín hiệu ngược đủ chuẩn thì đảo ngay; có hút lực từ đỉnh để bảo vệ lời\n"
                    f"⚖️ Cân bằng/lọc coin: Đã bỏ\n\n"
                    f"{get_strategy_config_text()}"
                )
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

ssl._create_default_https_context = ssl._create_unverified_context
