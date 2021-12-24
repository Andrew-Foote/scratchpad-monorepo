from __future__ import annotations

from collections import deque
from collections.abc import Callable, Iterable, Iterator
import itertools as it
from typing import TypeVar

T = TypeVar('T')

ChildrenMap = Callable[[T], Iterable[T]]

# A tree consists of a root of type T and a ChildrenMap of type T, which maps
# each vertex in the tree to its children. Although we prefer to pass in these
# two components directly rather than encapsulate them in a data type.

def bfs(children: ChildrenMap[T], root: T) -> Iterator[T]:
	"""A reference implementation of BFS (breadth-first search) for trees,
	which we will use as an oracle for testing."""
	queue = deque([root])

	while queue:
		vertex = queue.pop()
		yield vertex
		queue.extendleft(children(vertex))

def bfs2(children: ChildrenMap[T], root: T) -> Iterator[T]:
	"""The recursive implementation of BFS which we're interested in. It works
	in that it will yield the vertices in the tree in breadth-first order;
	however, its flaw is that once you ask it for the next vertex after it's
	yielded all the vertices, the iterator does not terminate but rather gets
	stuck in an infinite loop."""
	yield root

	for vertex in bfs(children, root):
		# now we go through the children, 
		yield from children(vertex)

def dfs(children: ChildrenMap[T], root: T) -> Iterator[T]:
	"""A recursive implementation of DFS (depth-first search), which I include
	here to show you how pleasingly parallel it is to the recursive
	implementation of BFS above. To exchange between the two, we just change
	the positions of (b/d)fs(children, ...) and children."""
	yield root

	for vertex in children(root):
		yield from dfs(children, vertex)

def bfs3(children: ChildrenMap[T], root: T) -> Iterator[T]:
	"""We can fix bfs3 by keeping track of how many vertices are at each level,
	and finishing once we get to a level with none. But this takes away some of
	the elegance of the implementation."""
	yield root
	breadth = 1
	iterator = bfs(children, root)

	while breadth:
		new_breadth = 0

		for vertex in it.islice(iterator, breadth):
			for child in children(vertex):
				yield child
				new_breadth += 1

		breadth = new_breadth

# testing

from dataclasses import dataclass
from typing import Generic
from hypothesis import given
import hypothesis.strategies as st

U = TypeVar('U')

@dataclass
class Tree(Generic[T]):
	label: T
	children: list[Tree[T]]

	def map(self, f: Callable[[T], U]) -> Tree[U]:
		return Tree(f(self.label), [child.map(f) for child in self.children])

Path = tuple[int, ...]

def path_labelled_tree(children: list[Tree[Path]]) -> Tree[Path]:
	return Tree(
		(),
		[child.map(lambda v: (i, *v)) for i, child in enumerate(children)]
	)

trees = st.recursive(
	st.just(path_labelled_tree([])),
	lambda trees: st.builds(path_labelled_tree, st.lists(trees))
)

@given(trees)
def test_bfs3_implements_bfs(tree):
	tree = (lambda tree: tree.children, tree)
	res, exp = (tuple(search(*tree)) for search in (bfs3, bfs))
	assert res == exp

# Maybe if we return info about the tree at the same time as we're doing our
# searches...

def dfsp(children: ChildrenMap[T], root: T) -> Iterator[T]:
	yield (), root

	for i, child in enumerate(children(root)):
		for path, vertex in dfsp(children, child):
			yield (i, *path), vertex

def bfsp(children: ChildrenMap[T], root: T) -> Iterator[T]:
	yield (), root

	for path, vertex in bfsp(children, root):
		for i, child in enumerate(children(vertex)):
			yield (*path, i), child

@given(trees)
def test_dfsp_reduces_to_dfs(tree):
	tree = (lambda tree: tree.children, tree)
	res, exp = (search(*tree) for search in (dfsp, dfs))
	assert tuple(vertex for path, vertex in res) == tuple(exp)

@given(trees)
def test_dfsp_yields_correct_paths(tree):
	tree = (lambda tree: tree.children, tree)
	assert all(path == vertex.label for path, vertex in dfsp(*tree))

# hm, don't think that helps much