"""
Functions for running simple genetic algorithms with one chromosome of fixed
length, with uniform probability of crossover along its length, and fitness-
proportionate parent selection probability.
"""

from typing import *
import numpy as np

def random_population(population_size: int, genome_size: int) -> np.ndarray:
    """
    Create a 2D `ndarray` with `population_size` rows and `genome_size`
    columns, populated with random booleans.

    Each row is intended to represent a distinct individual within a
    population, with the codon sequence for that individual being the array of
    booleans in the row.
    """
    return np.random.randint(
        2,
        size=(population_size, genome_size),
        dtype=bool
    )

def mutate(population: np.ndarray, p: Union[float, np.ndarray]) -> None:
    """
    Extra annotations:
      `population` should be a 2D `ndarray` of booleans.
      `p` should be a single float between 0 and 1 inclusive, or a 1D or 2D
      `ndarray` of such floats, which will be matched to `population`.

    Flip each boolean in `population` with probability given by the
    corresponding item of `p`.

    `population` is intended to represent a population (see the docstring for
    `random_population`) and the flips are intended to be interpreted as
    mutations of the codon sequences of the individuals within this
    population.
    """
    population ^= np.random.binomial(
        1,
        p,
        size=population.shape
    ).astype(bool)

def crossover(population: np.ndarray, p: float) -> None:
    """
    Extra annotations:
      `population` should be a 2D `ndarray` of booleans.
      `fitness` should be a single float, or a 1D `ndarray` of floats, which
      will be matched to `population`.
      `p` should be a single float between 0 and 1 inclusive.

    For each pair of adjacent rows in `population`, with probability `p`, swap
    the *n*-length final segments of the two rows, where *n* is an integer
    chosen uniformly from those between 1 and `population.shape[1]`,
    inclusive.

    `population` is intended to represent a population (see the docstring for
    `random_population`) and the swaps are intended to be interpreted as
    crossovers between the codon sequences of the individuals within this
    population.
    """

    # Each pair can be indexed by an integer between 0 and `half_size`
    # inclusive; the index of first individual in the pair within the actual
    # array is then twice this index. 
    is_crossover_pair = np.random.binomial(
        1,
        p,
        size=population.shape[0] // 2
    ).astype(bool)

    crossover_segment_sizes = iter(np.random.randint(
        1,
        population.shape[1],
        size=np.count_nonzero(is_crossover_pair)
    ))

    for i in range(0, population.shape[0], 2):
        if is_crossover_pair[i // 2]:
            segment_size = next(crossover_segment_sizes)
            tail1 = population[i, segment_size:].copy()
            tail2 = population[i + 1, segment_size:]
            tail1, tail2 = tail2, tail1.copy()

def regenerate(
    population: np.ndarray,
    fitness: Union[float, np.ndarray],
    crossover_p: float,
    mutation_p: Union[float, np.ndarray]
) -> np.ndarray:
    """
    Extra annotations:
      `population` should be a 2D `ndarray` of booleans.
      `fitness` should be a single float, or a 1D `ndarray` of floats, which
      will be matched to `population`.
      `crossover_p` should be a single float between 0 and 1 inclusive.
      `p` should be a single float between 0 and 1 inclusive, or a 1D or 2D
      `ndarray` of such floats, which will be matched to `population`.
        
    Replace the rows of `population` by randomly sampling from the original
    rows with replacement, with the probability of a row being selected in a
    given draw being proportional to the corresponding item in `fitness`
    (specifically, equal to the ratio of the item to the sum of all the
    items). Then, call `crossover` and `mutate` on the population (in that
    order).
    
    This can be interpreted as replacing the population with a new generation
    of individuals produced by mating the individuals in the original
    population.
    """

    population[:] = population[
        np.random.choice(
            np.arange(population.shape[0]),
            p=fitness / np.sum(fitness),
            size=population.shape[0]
        ),
        :
    ]

    crossover(population, crossover_p)
    mutate(population, mutation_p)

    return population

def evolve(
    population: np.ndarray,
    generation_count: int,
    crossover_p: float,
    mutation_p: Union[float, np.ndarray],
    fitness_f: Callable,
    data_f: Callable=None,
    **kwargs
) -> List[float]:
    if data_f is None:
        def data_f(population: np.ndarray, **kwargs):
            return np.mean(kwargs['fitness'])

    data = []
    generation = 0
    while True:
        #if generation > 0 and not generation % 10:
        #    print(f"generation {generation}")
        kwargs['fitness'] = fitness_f(population, **kwargs)
        data.append(data_f(population, **kwargs))
        if generation == generation_count - 1:
            return data
        regenerate(population, kwargs['fitness'], crossover_p, mutation_p)
        generation += 1

# Example fitness functions.

def hamming_weight(population: np.ndarray, **kwargs) -> np.ndarray:
    return np.sum(population, axis=1) + 1

def hamming_distance(
    population: np.ndarray,
    genome: np.ndarray
) -> np.ndarray:
    return np.sum(population ^ genome, axis=1) + 1

def mutual_hamming_distance(population: np.ndarray, **kwargs) -> np.ndarray:
    def f(individual):
        return np.mean(hamming_distance(population, individual))
    return np.apply_along_axis(f, 1, population)

def as_integer(population: np.ndarray, **kwargs):
    """Interpret each organism as an integer, by taking its codon sequence as
    the binary digits of the integer."""
    return population @ 2 ** np.arange(
        population.shape[1] - 1,
        -1,
        -1
    ) + 1

prisoners_dilemma_payoff = np.array([[1, 3], [0, 2]])

def memoryless_prisoners_dilemma(population: np.ndarray, genome: np.ndarray):
    def f(individual: np.ndarray):
        return np.sum(prisoners_dilemma_payoff[
            individual.astype(int),
            genome.astype(int)
        ])
    return np.apply_along_axis(f, 1, population)

def memoryless_mutual_prisoners_dilemma(population: np.ndarray, **kwargs):
    def f(individual: np.ndarray):
        return np.mean(memoryless_prisoners_dilemma(population, individual))
    return np.apply_along_axis(f, 1, population)

if __name__ == "__main__":
    import seaborn as sns
    import matplotlib.pyplot as plt
    population = random_population(10, 10)
    data = evolve(population, 10000, 0.005, 0.001, mutual_hamming_distance)
    plt.plot(data)
    #sns.lineplot(data=data)
    #plt.ylim(0, 12)
    plt.show()