from contextlib import contextmanager
from dataclasses import dataclass

ATOMIC_TYPES = {
    bool,
    int,
}

@dataclass
class VarTerm():
    : 

def match_case(x, a):
    """A generator which yields at most one value, which is the tuple of the
values of the placeholders in a which make the match.

    You can think of it as essentially trying to "flatten" x according to a
    "schema" given by a.

    match_case(0, 0)
        yields the empty tuple (there is a match, but no placeholders to assign)
    match_case(0, 1)
        doesn't yield
    """
    if isinstance(a, PatVar):
        yield x
    elif hasattr(a, '__match__'):
        yield from a.__match__(x) 
    elif hasattr(a, '__iter__'):
        subcases = [match_case(xi, ai) for xi, ai in zip(x, a)]

        try:
            for i, _ in enumerate(subcases):
                subcases[i] = next(subcases[i])
        except StopIteration:
            pass
        else:
            yield list(it.chain.from_iterable(subcases))
    else:
        if type(x) == type(a) and x == a:
            yield ()

@contextmanager
def match(x):
    yield lambda a: match_case(x, a), placeholder

def free_vars(t):
    with match(t) as (case, _):
        for x, in case(VarTerm(_)):
            return {x}

        for x, t in case(AbstTerm(_, _)):
            return free_vars(t) - {x}

        for t, u in case(AppTerm(_, _)):
            return free_vars(t) | free_vars(u)
