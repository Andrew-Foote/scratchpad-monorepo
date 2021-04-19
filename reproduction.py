import operator
import random
import numpy as np
import pygame

screen_dimensions = np.array((500, 500))
organisms = {}
new_organisms = {tuple(screen_dimensions // 2): np.array((255, 255, 255), dtype=np.uint8)}

pygame.init()
screen = pygame.display.set_mode(tuple(screen_dimensions))
time_at_last_update = pygame.time.get_ticks()
running = True

while running:
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False

    current_time = pygame.time.get_ticks()
    
    if current_time - time_at_last_update >= 100:
        for location, colour in organisms.items():
            if np.random.rand() < (3 * colour[0] - colour[1] - colour[2]) / 1024:
                direction = np.random.randint(-1, 2, size=2)
                new_location = np.array(location) + direction

                if np.all((0 <= new_location) & (new_location < screen_dimensions)):
                    new_colour = np.packbits(np.unpackbits(colour) ^ np.random.binomial(1, 1/576, size=24))
                    new_organisms[tuple(new_location)] = new_colour

        for location, colour in new_organisms.items():
            screen.set_at(location, tuple(colour))

        pygame.display.flip()
        organisms.update(new_organisms)
        new_organisms = {}
        time_at_last_update = current_time

pygame.quit()