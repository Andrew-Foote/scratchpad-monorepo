import adt
import attr
import dpcontracts as dpc # type: ignore
import functools as ft
import string
import typing as t

@attr.s(auto_attribs=True, frozen=True, slots=True)
class Var:
	ident: int

	def __str__(self):
		subscript, letter_index = divmod(self.ident, 26)
		subscript = str(subscript) if subscript else ''
		return string.ascii_lowercase[letter_index] + subscript

@adt.adt
class Term:
	VAR: adt.Case[Var]
	ABST: adt.Case[Var, 'Term']
	APP: adt.Case['Term', 'Term']

	def is_var(self):
		return self.match(
			var=lambda x: True,
			abst=lambda x, t: False,
			app=lambda t, u: False
		)

	def is_abst(self):
		return self.match(
			var=lambda x: False,
			abst=lambda x, t: True,
			app=lambda t, u: False
		)

	def is_app(self):
		return self.match(
			var=lambda x: False,
			abst=lambda x, t: False,
			app=lambda t, u: True
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
