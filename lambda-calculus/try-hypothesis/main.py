import adt
import attr
import functools as ft
import typing as t

Var = t.NewType('Var', str)

@adt.adt
class Term:
	VAR: adt.Case[Var]
	ABST: adt.Case[Var, 'Term']
	APP: adt.Case['Term', 'Term']

	def free_vars(self) -> t.Set[Var]:
		return self.match(
			var=lambda x: {x},
			abst=lambda x, t: t.free_vars() - {x},
			app=lambda t, u: t.free_vars() | u.free_vars()
		)

	def has_free(self, var: Var) -> bool:
		return self.match(
			var=lambda x: x == var,
			abst=lambda x, t: x != var and t.has_free(var),
			app=lambda t, u: t.has_free(var) or u.has_free(var)
		)
