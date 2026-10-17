"""Backward-compatible launcher: python solar.py."""
if __name__ == '__main__':
    import runpy
    runpy.run_module('solar_mining.controller', run_name='__main__')
else:
    import sys
    from solar_mining import controller
    sys.modules[__name__] = controller
