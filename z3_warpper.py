import z3
from rich.logging import RichHandler
import logging

FORMAT = "%( message )s"
logging.basicConfig(level="DEBUG", datefmt="[%X]", handlers=[RichHandler(markup=True)])
log = logging.getLogger("cpfg.z3_warpper")


# Apply sign extend when use s.add()
def equal(s, x, y):
    if x.size() < y.size():
        log.debug("ext")
        s.add(z3.SignExt(y.size() - x.size(), x) == y)
    elif x.size() > y.size():
        log.debug("ext")
        s.add(z3.SignExt(x.size() - y.size(), y) == x)
    else:
        log.debug("un ext")
        s.add(x == y)
