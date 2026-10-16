# ☀️ Solar Mining

**Automatizált napelem monitorozás és bányászatvezérlés**  
Ez a projekt egy napelemes rendszer állapotának figyelésére, adatgyűjtésére és bányászgépek vezérlésére szolgál. Tartalmaz Python szkripteket, Jupyter notebookot, konfigurációs fájlokat, valamint egy Docker-alapú környezetet.

---

## unMineable USDT (PearlPow)

A vezérlő mostantól az **unMineable USDT** fiók `solarminer` nevű,
**PearlPow** algoritmusú workerét figyeli. Alapértelmezett cím:

https://unmineable.com/address/0xaedac36dcfc956864fcc03ec2ef256facaefd991?coin=USDT

- `WALLET_ADDRESS`: USDT EVM-cím vagy a teljes unMineable USDT URL.
  Üres vagy régi RVN-beállítás esetén a fenti cím az alapértelmezett.
  A mentett RVN-cím nem állítja vissza a régi poolt.
- `MY_MINING_ALGORITHM`: alapértelmezésben `pearlpow`.
- `MY_MINING_WORKER`: alapértelmezésben `solarminer`; üres értékkel az adott
  algoritmus összes workerének jelentett hashrátája összegezhető.
- A `/wallet <cím vagy URL>` Telegram-parancs USDT EVM-címet fogad el.
- API: `https://api.unmineable.com/v5/address/<cím>?coin=USDT`, majd
  `/v5/account/<uuid>/workers`. A jelentett `rhr` érték H/s-ban érkezik;
  a kijelzés automatikusan kH/s–PH/s egységre vált. Az offline workerek
  korábbi hashrátája nem számít aktív termelésnek. API-hiba esetén nincs
  automatikus újraindítás; a megerősített nulla hashráta továbbra is kiváltja
  a konfigurált védelmet.

Ez a projekt a monitorozást és a GPIO-alapú gépvezérlést végzi, nem indít
bányászprogramot. A tényleges bányászprogram poolját és USDT kifizetési címét
a bányászgépen kell beállítani. A képernyőképen jelzett kifizetési hálózat BSC;
ezt a beállítást az unMineable fiók kezeli.

### Fejlesztés és ellenőrzés

A `requirements.txt` a frissítéskor elérhető legújabb stabil közvetlen Python
függőségeket rögzíti. Ellenőrzött Python-verzió: 3.11.
A dashboard Chart.js 4.5.1 és Font Awesome 7.3.1 verziót használ.

```bash
python -m pip install -r requirements.txt
python -m pip check
python -m unittest -v test_mining_pool
python simulate_decisions.py --telemetry telemetry_history_20260524_161647.json --history-dir solarman_json
```

A tesztek helyettesített API-válaszokkal futnak, nem vezérelnek hardvert.
Élő ellenőrzéshez engedélyezni kell az `api.unmineable.com` HTTPS-elérését.

## 🚀 Fő funkciók

- 🔋 **Valós idejű napelem adatok lekérése** (`solar.py`, `solarman.ipynb`)
- 📊 **Adatok tárolása és elemzése** (`solarman_data.json`, `state.json`, `quote_usage.json`)
- 🐳 **Könnyű telepítés Docker Compose segítségével**
- 🔐 `.env` támogatás környezeti változókhoz

---

## 🗂 Fájlszerkezet

| Fájl / Könyvtár       | Leírás |
|------------------------|--------|
| `solar.py`             | Fő Python szkript a napenergia figyeléshez |
| `solarman.ipynb`       | Jupyter notebook a napelem adatokkal való kísérletezéshez |
| `solarman_data.json`   | Lekért Solarman API adatok |
| `state.json`           | Rendszerállapot cache |
| `quote_usage.json`     | API használat naplózása |
| `docker-compose.yml`   | Docker Compose konfiguráció |
| `dockerfile`           | Egyedi Docker image build fájl |
| `requirements.txt`     | Python csomagok listája |
| `.env`                 | Környezeti változók definíciója |
| `README.md`            | Dokumentáció |

---

## 🐳 Telepítés (Docker-rel)

1. Klónozd a repót:
   ```bash
   git clone https://github.com/felhasznalonev/solar_mining.git
   cd solar_mining


## 🌐 LAN elérés név alapján

A `docker-compose.yml` már beállítja a konténer hostname-jét `solarminer`-re és hálózati alias-t is ad.
Ha a kliensek DNS-e a Pi-hole-t (vagy ugyanazt a docker hálózati DNS-t) használja, akkor a dashboard elérhető név alapján is:

```bash
http://solarminer:9000
```

Ha ez nem oldódik fel kliens oldalon, akkor a router/Pi-hole DNS-ben készíts egy `solarminer` A rekordot a host IP-jére (pl. `192.168.0.197`).
