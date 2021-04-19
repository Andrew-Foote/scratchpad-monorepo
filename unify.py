from abc import ABC, abstractmethod
from dataclasses import dataclass

@dataclass(frozen=True)
class FunSymbol:
    ident: str

    def __call__(self, *args):
        return App(self, args)

class Term(ABC):
    @abstractmethod
    def contains_var(self, x: 'Var') -> bool:
        ...

    @abstractmethod
    def subst(self, s: dict['Var', 'Term']) -> 'Term':
        ...

@dataclass(frozen=True)
class Var(Term):
    ident: str

    def contains_var(self, x):
        return self == x

    def subst(self, s):
        return s.get(self, self)
    
@dataclass(frozen=True)
class App(Term):
    fun: FunSymbol
    args: tuple[Term, ...]

    def contains_var(self, x):
        return any(arg.contains_var(x) for arg in self.args)

    def subst(self, s):
        return App(self.fun, tuple(arg.subst(s) for arg in self.args))

def unify(*eqns: tuple[Term, Term]) -> dict[Var, Term]:
    """Returns a unifier (represented as a dictionary) of the given equations
    (represented as 2-tuples).

    >>> f = FunSymbol('f')
    >>> x = Var('x')
    >>> y = Var('y')
    >>> s = unify((f(x, y), f(y, x)))
    >>> len(s)
    1
    >>> x.subst(s) == y.subst(s)
    True
    >>> z = Var('z')
    >>> s = unify((f(f(x, y), f(y, x)), f(z, z)))
    >>> len(s)
    2
    >>> x.subst(s) == y.subst(s)
    True
    >>> z.subst(s) == f(x, y).subst(s)
    True
    """
    unifier = {}
    eqns = list(eqns)

    while eqns:
        lhs, rhs = eqns.pop()

        if lhs == rhs:
            continue

        if isinstance(lhs, App):
            if isinstance(rhs, App):
                # the length check can be omitted if each function symbol
                # takes a fixed number of arguments
                if lhs.fun == rhs.fun and len(lhs.args) == len(rhs.args):
                    eqns.extend((l, r) for l, r in zip(lhs.args, rhs.args))
                    continue
                
                raise ValueError(
                    f'{lhs} and {rhs} are not unifiable since they are '
                    'applications of different function symbols'
                )

            assert isinstance(rhs, Var), rhs
            lhs, rhs = rhs, lhs

        assert isinstance(lhs, Var), lhs

        if rhs.contains_var(lhs):
            raise ValueError(
                f'the variable {lhs} occurs in the term {rhs} and hence is not'
                ' unifiable with it'
            )

        s = {lhs: rhs}

        for i, (lhs, rhs) in enumerate(eqns):
            eqns[i] = (lhs.subst(s), rhs.subst(s))

        for x, t in unifier.items():
            unifier[x] = t.subst(s)

        unifier |= s

    return unifier

if __name__ == '__main__':
    import doctest
    doctest.testmod()
