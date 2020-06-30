from adt import adt, Case
import itertools as it
import typing as t
import typing_extensions as tx

_T = t.TypeVar('_T')
_U = t.TypeVar('_U')

@adt
class Maybe(t.Generic[_T]):
	NOTHING: Case
	JUST: Case[_T]

	def is_nothing(self): return self.match(nothing=lambda: True, just=lambda x: False)
	def is_just(self): return self.match(nothing=lambda: False, just=lambda x: True)

	def map1(self, f: t.Callable[[_T], _U]) -> 'Maybe[_U]':
		return self.match(
			nothing=lambda: Maybe[_U].NOTHING(),
			just=lambda x: Maybe[_U].JUST(f(x))
		)

	# sadly I this is the best we can do for the type signature; ideally we'd be able to express
	# that each (kw)arg of the callback should be of the same type as the corresponding (kw)arg
	# passed to map
	@staticmethod
	def map(
		f: t.Callable[..., _U],
		*args: 'Maybe', **kwargs: 'Maybe'
	) -> 'Maybe[_U]':
		return (
			Maybe.NOTHING()
			if Maybe.NOTHING() in it.chain(args, kwargs.values())
			else Maybe.JUST(f(
				*(arg.just() for arg in args),
				**{k: arg.just() for k, arg in kwargs.items()}
			))
		)