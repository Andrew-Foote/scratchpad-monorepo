from dataclasses import dataclass
import dpcontracts as dpc
import itertools as it
import typing as t

def assert_never(x: t.NoReturn) -> t.NoReturn:
	raise AssertionError(f'invalid value: {x!r}')

@dataclass(frozen=True)
class TermVar:
	name: str

Term = t.Union[TermVar, 'FunApp']

#@dpc.invariant('arity must be nonnegative', lambda self: self.arity >= 0)
@dataclass(frozen=True)
class FunSymbol:
	name: str
	arity: int

#@dpc.invariant('number of arguments must match arity', lambda self: len(self.args) == self.symbol.arity)
@dataclass(frozen=True)
class FunApp:
	symbol: FunSymbol
	args: t.Tuple[Term, ...]

Formula = t.Union[
	'RelApp',
	'Connect',
	'Quantify'
]

#@dpc.invariant('arity must be nonnegative', lambda self: self.arity >= 1)
@dataclass(frozen=True)
class RelSymbol:
	name: str
	arity: int

#@dpc.invariant('number of arguments must match arity', lambda self: len(self.args) == self.symbol.arity)
@dataclass(frozen=True)
class RelApp:
	symbol: RelSymbol
	args: t.Tuple[Term, ...]

#@dpc.invariant('arity must be nonnegative', lambda self: self.arity >= 0)
@dataclass(frozen=True)
class Connective:
	name: str
	arity: int

#@dpc.invariant('number of arguments must match arity', lambda self: len(self.args) == self.symbol.arity)
@dataclass(frozen=True)
class Connect:
	symbol: Connective
	args: t.Tuple[Formula, ...]

@dataclass(frozen=True)
class Quantifier:
	name: str

@dataclass(frozen=True)
class Quantify:
	symbol: Quantifier
	bound_var: TermVar
	scope: Formula

def is_free(x, s):
	if isinstance(s, TermVar):
		return x == s
	elif isinstance(s, (FunApp, RelApp, Connect)):
		return any(is_free(x, t) for t in s.args)
	elif isinstance(s, Quantify):
		return not x == s.bound_var and is_free(x, s.scope)
	else:
		assert_never(s)

def fresh_var(string):
	for n in it.count():
		var = TermVar(name=str(n))

		if not is_free(var, string):
			return var

class VariableCapture:
	pass

def subst(t, x, s):
	if s == x:
		return t
	elif isinstance(s, TermVar):
		return s
	elif isinstance(s, FunApp):
		return FunApp(s.symbol, tuple(subst(t, x, arg) for arg in s.args))
	elif isinstance(s, RelApp):
		return RelApp(s.symbol, tuple(subst(t, x, arg) for arg in s.args))
	elif isinstance(s, Connect):
		return Connect(s.symbol, tuple(subst(t, x, arg) for arg in s.args))
	elif isinstance(s, Quantify):
		if not is_free(x, s):
			return s
		elif is_free(s.bound_variable, t):
			raise VariableCapture
		else:
			return Quantify(s.symbol, s.bound_var, subst(t, x, s.scope))
	else:
		assert_never(s)