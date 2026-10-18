"""Atomic, bounded 24-hour display history; never used to train the planner."""
import json
import os
from datetime import datetime, timedelta
from pathlib import Path
from threading import RLock


class RecentHistory:
    def __init__(self, path):
        self.path = Path(path)
        self.lock = RLock()
        self.loaded = False
        self.rows = []

    def _refresh(self, now):
        if not self.loaded:
            try:
                data = json.loads(self.path.read_text())
                self.rows = data if isinstance(data, list) else []
            except (OSError, ValueError):
                self.rows = []
            self.loaded = True
        valid = {}
        for row in self.rows:
            try:
                at = datetime.fromisoformat(row['ts'])
                if now - timedelta(hours=24) <= at <= now:
                    valid[at] = row
            except (KeyError, TypeError, ValueError):
                continue
        rows = [valid[at] for at in sorted(valid)][-2880:]
        changed = rows != self.rows
        self.rows = rows
        return changed

    def _save(self):
        temporary = self.path.with_suffix('.tmp')
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            temporary.write_text(json.dumps(self.rows, ensure_ascii=False, allow_nan=False))
            os.replace(temporary, self.path)
        except (OSError, ValueError) as err:
            print(f'[Last 24 hours] Could not save display history: {err}')

    def append(self, row, now):
        with self.lock:
            self._refresh(now)
            self.rows.append(row)
            self._refresh(now)
            self._save()

    def snapshot(self, now):
        with self.lock:
            if self._refresh(now):
                self._save()
            return [dict(row) for row in self.rows]
