import adt
import attr
import dpcontracts as dpc # type: ignore
import functools as ft
import typing as t
from maybe import Maybe

def ascii_lower_from_index(i: int) -> str:
	return chr(97 + i)

def ascii_lower_to_index(c: str) -> int:
	return ord(c) - 97

@attr.s(auto_attribs=True, frozen=True, slots=True)
class Var:
	ident: int

	def __str__(self):
		subscript, letter_index = divmod(self.ident, 26)
		subscript = str(subscript) if subscript else ''
		return ascii_lower_from_index(letter_index) + subscript

def parse_var(s: str, i: int) -> t.Tuple[t.Optional[Var], int]:
	if not (i < len(s) and ord('a') <= ord(s[i]) <= ord('z')):
		return None, i

	letter_index = ascii_lower_to_index(s[i])	
	i += 1
	subscript = 0

	if not (i < len(s) and ord('1') <= ord(s[i]) <= ord('9')):
		return Var(letter_index), i
	
	subscript += int(s[i])
	i += 1

	while i < len(s) and ord('0') <= ord(s[i]) <= ord('9'):
		subscript *= 10
		subscript += int(s[i])
		i += 1

	return Var(subscript * 26 + letter_index), i

@adt.adt
class Term:
	VAR: adt.Case[Var]
	ABST: adt.Case[Var, 'Term']
	APP: adt.Case['Term', 'Term']

	def is_var(self) -> bool:
		return self.match(
			var=lambda x: True,
			abst=lambda x, t: False,
			app=lambda t, u: False
		)

	def is_abst(self) -> bool:
		return self.match(
			var=lambda x: False,
			abst=lambda x, t: True,
			app=lambda t, u: False
		)

	def is_app(self) -> bool:
		return self.match(
			var=lambda x: False,
			abst=lambda x, t: False,
			app=lambda t, u: True
		)

	@dpc.ensure(
		'Parsing the stringification of a term returns the original term',
		lambda args, result: parse(result) == args.self
	)
	def __str__(self):
		return self.match(
			var=lambda x: str(x),
			abst=lambda x, t: f'λ{x}.{t}',
			app=lambda t, u: (
				(f'({t})' if t.is_abst() else str(t))
				+ (f'({u})' if u.is_abst() or u.is_app() else str(u))
			)
		)

	def free_vars(self) -> t.Set[Var]:
		return self.match(
			var=lambda x: {x},
			abst=lambda x, t: t.free_vars() - {x},
			app=lambda t, u: t.free_vars() | u.free_vars()
		)

	@dpc.ensure(
		'term.has_free(var) <==> var in term.free_vars()',
		lambda args, result: result == (args.var in args.self.free_vars())
	)
	def has_free(self, var: Var) -> bool:
		return self.match(
			var=lambda x: x == var,
			abst=lambda x, t: x != var and t.has_free(var),
			app=lambda t, u: t.has_free(var) or u.has_free(var)
		)

	@dpc.ensure(
		'term.has_free(var) ==> term.has_substitutable(var, repl)',
		lambda args, result: not args.self.has_free(args.var) or result
	)
	def has_substitutable(self, var: Var, repl: 'Term') -> bool:
		return self.match(
			var=lambda x: True,
			abst=lambda x, t: (
				x == var
				or not t.has_free(var)
				or (not repl.has_free(x) and t.has_substitutable(var, repl))
			),
			app=lambda t, u: (t.has_substitutable(var, repl) and u.has_substitutable(var, repl))
		)

	@dpc.ensure(
		'term.has_substitutable(var, repl) <==> term.maybe_subst(var, repl) == Maybe.NOTHING()',
		lambda args, result: result.is_just() == args.self.has_substitutable(var, repl)
	)
	@dpc.ensure(
		'term.has_free(var) ==> term.maybe_subst(var, repl) == Maybe.JUST(term)',
		lambda args, result: not args.self.has_free(args.var) or result == args.self
	)
	def maybe_subst(self, var: Var, repl: 'Term') -> Maybe['Term']:
		return self.match(
			var=lambda x: (
				Maybe.JUST(repl)
				if x == var
				else Maybe.JUST(self)
			),
			abst=lambda x, t: (
				Maybe.JUST(self)
				if x == var or not free(var, self)
				else Maybe.NOTHING()
				if free(x, repl)
				else t.maybe_subst(var, repl).map1(lambda u: Term.ABST(x, u))
			),
			app=lambda t, u: Maybe.map(
				lambda t_, u_: Term.APP(t_, u_),
				t.maybe_subst(var, repl), u.maybe_subst(var, repl)
			)
		)

	def subst(self, var: Var, repl: 'Term') -> 'Term':
		def var(x):
			if x == var:
				return repl
			
			return self
		
		def abst(x, t):
			if x == var or not free(var, self):
				return self

			y = fresh_var({var} | repl.free_vars() | t.free_vars())
			# why is this true? well, it's implied by y not being free in t
			assert t.has_substitutable(x, y)
			u = t.subst(x, y)
			# why is this true? well, it'd be implied by var not being free in u
			# maybe we have to do the capture avoidance here
			# but why do we need y 
			assert u.has_substitutable(var, repl)
			return Term.ABST(y, u.subst(var, repl))

		def app(t, u):
			return Term.APP(t.subst(var, repl), u.subst(var, repl))

		return self.match(var, abst, app)

@attr.s(auto_attribs=True, frozen=True, slots=True)
class ParserFrame:
	params: t.List[Var]
	bodies: t.List[Term]

	def term(self) -> Term:
		...

def parse_term(s: str, i0: int) -> t.Tuple[Term, int]:
	i = i0
	params = []

	while i < len(s) and s[i] == 'λ':
		var, i = parse_var(s, i + 1)
		if var is None: raise ValueError(f'expected a variable at index {i}, after the λ')
		params.append(var)
		if i >= len(s) or s[i] != '.': raise ValueError(f'expected a . at index {i}, after the binder')
		i += 1

	bodies = []

	while i < len(s):
		if s[i] == '(':
			term, i = parse_term(s, i + 1)
			bodies.append(term)
		elif s[i] == ')':
			i += 1
			break
		else:
			var, i = parse_var(s, i)
			if var is None: raise ValueError(f'expected (, ) or a variable at index {i}')
			bodies.append(Term.VAR(var))

	if not bodies:
		raise ValueError(f'expected a term at index {i0}')

	term = bodies[0]
	for body in bodies[1:]: term = Term.APP(term, body)
	params.reverse()
	for param in params: term = Term.ABST(param, term)
	return term, i

def parse(s: str) -> Term:
	term, i = parse_term(s, 0)
	if i < len(s): raise ValueError(f'unmatched closing parenthesis at index {i - 1}')
	return term