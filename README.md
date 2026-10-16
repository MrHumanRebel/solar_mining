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
  a kijelzés automatikusan kH/s–PH/s egységre vált. Ez kizárólag tájékoztató
  adat, idle állapotban is frissül. Sem pozitív, sem nulla, sem hibás
  pool-hashráta nem válthat ki GPIO-műveletet.

Ez a projekt a monitorozást és a GPIO-alapú gépvezérlést végzi, nem indít
bányászprogramot. A tényleges bányászprogram poolját és USDT kifizetési címét
a bányászgépen kell beállítani. A képernyőképen jelzett kifizetési hálózat BSC;
ezt a beállítást az unMineable fiók kezeli.

### Fogyasztásalapú automatikus leállítás

A `miner_power_guard.py` a két tápkörös, 5× RTX3070 géphez tartozó
L2/L3 fogyasztásnövekedést tanulja meg; a 3 GPU és a 2 GPU + CPU ág
mindkét fáziskiosztása támogatott. A pool API nem vesz részt a vezérlésben.

- Három friss, stabil STOP-mérés adja az alapfogyasztást. Saját indítás után
  két, legalább két perc különbséggel érkező mérésnek kell igazolnia a páros
  L2/L3 emelkedést, lényeges L1-változás nélkül. Az együttes többlet
  500–1000 W, a 3 GPU-s ág 250–550 W, a másik 200–650 W lehet.
- STOP-kérés után **1000 W feletti teljes fogyasztás ÉS a megtanult L2/L3
  terhelés** szükséges három egymást követő, legalább két percenkénti mérésben.
  Az alapértelmezett ötperces ciklussal ez körülbelül tíz perc megerősítés.
- Futásonként legfeljebb egy automatikus hosszú gombnyomás engedélyezett.
  Bármelyik azonosított ág eltűnése visszavonja a felismerést: későbbi
  sütő/főzőlap-terhelés nem élesíti újra ugyanazt a futást.
- A sima állapotváltás sem küld többé vakon hosszú gombnyomást. A kézi
  Telegram/GUI-parancsok továbbra is közvetlen parancsok.
- Hiányzó adatok, hat percnél régebbi vagy ismételt mérés, hét percnél
  hosszabb mérési rés, bizonytalan terhelés vagy alkalmazás-újraindítás után
  nincs automatikus gombnyomás. Újraindítás után új, megfigyelt indítás kell.
- Friss `collectionTime` (másodperc/milliszekundum), `dataTime` vagy
  `timestamp`, explicit teljes fogyasztási mező és mindhárom fázis szükséges.
  Inverterkimenet csak akkor használható fázisterhelési közelítésként, ha a
  fázisösszeg és a teljes fogyasztás eltérése legfeljebb 100 W vagy 10%.
  Nappali cache/fallback adatból nincs automatikus leállítás. Idle alatt is
  történik friss Solarman-lekérés, ami beleszámít az API-kvótába.

A felismerés oka a `[Power guard]` naplóban és a snapshot API
`power_guard_reason` mezőjében látszik. Ez konzervatív heurisztika:
összesített fázismérésből nem bizonyítható egy fogyasztó azonossága. A két
bányásztáp külön fogyasztásmérője szükséges a biztos elkülönítéshez.

### Fejlesztés és ellenőrzés

A `requirements.txt` a frissítéskor elérhető legújabb stabil közvetlen Python
függőségeket rögzíti. Ellenőrzött Python-verzió: 3.11.
A dashboard Chart.js 4.5.1 és Font Awesome 7.3.1 verziót használ.

```bash
python -m pip install -r requirements.txt
python -m pip check
python -m unittest -v test_mining_pool test_miner_power_guard
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
