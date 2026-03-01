# ☀️ Solar Mining

**Automatizált napelem monitorozás és bányászatvezérlés**  
Ez a projekt egy napelemes rendszer állapotának figyelésére, adatgyűjtésére és bányászgépek vezérlésére szolgál. Tartalmaz Python szkripteket, Jupyter notebookot, konfigurációs fájlokat, valamint egy Docker-alapú környezetet.

---

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
