#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>
#include <stdbool.h>

#define MAX(x, y) (((x) > (y)) ? (x) : (y))

#include "cubiomes/rng.h"
#include "cubiomes/finders.h"

typedef enum {
    STRUCTURE, BIOME, PILLAR
} ConstraintType;

typedef struct {
    ConstraintType tp; 

    int type;
    int x, z;
    
    int chunk_range, offset_x, offset_z, reg_x, reg_z;
    uint64_t salt;
} Constraint;

#define STRUCTURE_CONSTRAINT(t, _x, _z) (Constraint){.tp=STRUCTURE, .type=t, .x=_x, .z=_z}
#define BIOME_CONSTRAINT(t, _x, _z) (Constraint){.tp=BIOME, .type=t, .x=_x, .z=_z}
#define PILLAR_CONSTRAINT(seed) (Constraint){.tp=PILLAR, .type=seed}

typedef struct {
    Constraint *cons;
    size_t length;
} Constraints;

void parse_constraints(Constraints constraints) {
    if (constraints.length < 1) {
        fprintf(stderr, "ERROR: You need at least one constraint!");
        exit(1);
    }

    StructureConfig conf;
    int total_bits = 0;
    for (size_t i = 0; i < constraints.length; i++) {
        Constraint *c = &constraints.cons[i];
        if (c->tp != STRUCTURE) { // only structure constraints need to be parsed :D
            continue;
        }
    
        getStructureConfig(c->type, MC_1_21_3, &conf);
        c->salt = conf.salt;
        c->chunk_range = conf.chunkRange;
        
        int cx = c->x >> 4;
        int cz = c->z >> 4;

        int _cx = cx < 0 ? cx - conf.regionSize + 1 : cx;
        int _cz = cz < 0 ? cz - conf.regionSize + 1 : cz;

        c->reg_x = floor(_cx / conf.regionSize);
        c->reg_z = floor(_cz / conf.regionSize);

        c->offset_x = cx - (c->reg_x * conf.regionSize);
        c->offset_z = cz - (c->reg_z * conf.regionSize);

        total_bits += (int)log2((conf.chunkRange) & (-conf.chunkRange)) * 2;
    }
    if (total_bits < 20) {
        fprintf(stderr, "WARNING: Not enough bits to narrow down structure seed! (%d/%d)\n", total_bits, 20);
        // exit(1);
    }
}

uint64_t gcd(uint64_t a, uint64_t b) {
    if (a == 0)
        return b;
    if (b == 0)
        return a;
    if (b == 0)
        return a;
    if (a == b)
        return a;
    if (a > b)
        return gcd(a - b, b);
    return gcd(a, b - a);
}

inline void goBack2(uint64_t* rand) {
    *rand = (*rand * 254681119335897ULL + 120305458776662ULL) & MASK48;
}

inline void goBack(uint64_t* rand) {
    *rand = (*rand * 246154705703781ULL + 107048004364969ULL) & MASK48;
}

// stolen from https://github.com/michel-leonard/C-MathSnip/blob/main/mod_inv.c :)
uint64_t modinv(uint64_t ra, uint64_t rb) {
    uint64_t rc, sa = 1, sb = 0, sc, i = 0;
    if (rb > 1) do {
            rc = ra % rb;
            sc = sa - (ra / rb) * sb;
            sa = sb, sb = sc;
            ra = rb, rb = rc;
        } while (++i, rc);
    sa *= (i *= ra == 1) != 0;
    sa += (i & 1) * sb;
    return sa;
}

typedef struct {
    uint64_t *seeds;
    size_t size;
} Seeds;

Seeds solve_constraints_for_structure_seeds(Constraints constraints) {
    int max = 0;
    for (size_t i = 0; i < constraints.length; i++) {
        if ((int)log2(constraints.cons[i].chunk_range & -constraints.cons[i].chunk_range)) {
            max = MAX(max, constraints.cons[i].chunk_range);
        }
    }
    int mp = max & -max; 
    int lp = (int)log2(mp);

    int num_lower = 0;
    uint64_t *valid_lower = malloc(sizeof(uint64_t) * (int)((3.0/100.0) * (1<<(17 + lp))));
    // huge thank you to Kris for his great writeup on bitlifing: https://github.com/Kludwisz/BitLifting/
    for (uint64_t lower = 0; lower < 1ull<<(17 + lp); lower++) {
        for (size_t i = 0; i < constraints.length; i++) {
            Constraint c = constraints.cons[i];
            if (c.tp != STRUCTURE) {
                continue;
            }
            int p = c.chunk_range & (-c.chunk_range);
            if (p < 2) {
                continue;
            }
            uint64_t lower_seed = ((uint64_t)c.reg_x*341873128712ULL + (uint64_t)c.reg_z*132897987541ULL + lower + (uint64_t)c.salt);
            setSeed(&lower_seed, lower_seed);
            if (nextInt(&lower_seed, c.chunk_range) % p != c.offset_x % p || nextInt(&lower_seed, c.chunk_range) % p != c.offset_z % p) {
                goto next_lower;
            }
        }
        valid_lower[num_lower] = lower;
        num_lower++;
next_lower:
        ;
    }

    uint64_t *structure_seeds = (uint64_t *)malloc(sizeof(uint64_t) * 0); // might need more room than this!
    int num_structure_seeds = 0;

    // this code is experimental: (not anymore!)
    // we need to find the best constraint to reverse on
    max = 0;
    size_t best_index = -1;
    for (size_t i = 0; i < constraints.length; i++) {
        Constraint *c = &constraints.cons[i];
        uint64_t param = c->chunk_range / gcd(8, c->chunk_range);
        if (param > (uint64_t)max) {
            best_index = i;
            max = (int)param;
        }
    }
    Constraint c = constraints.cons[best_index];

    for (int i = 0; i < num_lower; i++) {
        uint64_t lower20 = valid_lower[i];
        uint64_t region_lower20 = (((uint64_t)c.reg_x*341873128712ULL + (uint64_t)c.reg_z*132897987541ULL + lower20 + (uint64_t)c.salt)) & 0xFFFFF;
        setSeed(&region_lower20, region_lower20);

        int x = nextInt(&region_lower20, c.chunk_range);
        int z = nextInt(&region_lower20, c.chunk_range);
        (void)x;
        (void)z;
        region_lower20 = region_lower20 & 0xFFFFF; 
        // could do a sanity check here?

        /*
            We need to find the full region seed given the lower20
            naive: 28 bit bruteforce
            better:
                given the lower20, we know the z coordinate takes the form: upper31 ≡ Z mod C
                U = upper28
                L3 = upper3 of lower20
                upper31 = (U << 3) | L3
                U * 8 + L3 ≡ Z (mod C)
                U * 8 ≡ Z - L3 (mod C)
                let d = gcd(8, C)
                (8 / d) U ≡ (Z - L3) / d (mod C / d)
                U ≡ (8 / d)^(-1) ((Z - L3) / d) (mod C / d)
                => U = (C / d)k + (8 / d)^(-1) ((Z - L3) / d) k∈ℤ
                perfect!
        */

        // consistancy with above
        uint64_t L3 = (region_lower20 >> 17) & 0x7;
        uint64_t C = c.chunk_range;
        uint64_t Z = c.offset_z;
        uint64_t d = gcd(8, C);

        uint64_t reduced_mod = C / d;
        uint64_t inv = modinv(8 / d, C / d);
        uint64_t basis = inv * ((Z - L3) / d) % reduced_mod;
        uint64_t end = (1ull<<28) - 1;
        for (uint64_t upper28 = basis; upper28 < end; upper28 += reduced_mod) {
            uint64_t full_region_seed = (upper28 << 20) | region_lower20; 
            goBack2(&full_region_seed);
            int x = nextInt(&full_region_seed, c.chunk_range);
            int z = nextInt(&full_region_seed, c.chunk_range);
            if (x != c.offset_x || z != c.offset_z) { // the second part should never really happen, just a sanity check...
                continue;
            }
            goBack2(&full_region_seed);

            full_region_seed ^= 0x5deece66d;
            uint64_t structure_seed = (full_region_seed - c.reg_x * 341873128712ULL - c.reg_z * 132897987541ULL - (uint64_t)c.salt) & MASK48;

            for (size_t i = 0; i < constraints.length; i++) {
                Constraint *c = &constraints.cons[i];

                if (c->tp == PILLAR) {
                    uint64_t ss = structure_seed;
                    if ((nextLong(&ss) & 65535) != (uint64_t)c->type) {
                        goto next_upper_1;
                    }
                }
                if (c->tp != STRUCTURE) {
                    continue;
                }

                uint64_t ss = structure_seed;
                setSeed(&ss, c->reg_x*341873128712ull + c->reg_z*132897987541ull + ss + (uint64_t)c->salt);
                if (nextInt(&ss, c->chunk_range) != c->offset_x || nextInt(&ss, c->chunk_range) != c->offset_z) {
                    goto next_upper_1;
                }
            }
            num_structure_seeds++;
            structure_seeds = (uint64_t *)realloc(structure_seeds, sizeof(uint64_t) * num_structure_seeds);
            structure_seeds[num_structure_seeds - 1] = structure_seed;
next_upper_1:
            ;
        }
    }

    free(valid_lower);
    return (Seeds){.seeds=structure_seeds, .size=num_structure_seeds};
}

Seeds solve_constraints_for_world_seeds(Constraints constraints, Seeds structure_seeds) {
    Generator g;
    setupGenerator(&g, MC_1_21_3, 0);

    uint64_t *seeds = malloc(sizeof(uint64_t) * 0);
    size_t num_seeds = 0;

    for (size_t i = 0; i < structure_seeds.size; i++) {
        uint64_t structure_seed = structure_seeds.seeds[i];
        for (uint64_t upper = 0; upper < 0x10000; upper++) {
            uint64_t world_seed = structure_seed | (upper << 48);
            applySeed(&g, DIM_OVERWORLD, world_seed);
            for (size_t j = 0; j < constraints.length; j++) {
                Constraint *c = &constraints.cons[j];

                switch (c->tp) {
                    case STRUCTURE: {
                        Pos p;
                        getStructurePos(c->type, MC_1_21_3, world_seed, c->reg_x, c->reg_z, &p);
                        if (p.x >> 4 != c->x >> 4 || p.z >> 4 != c->z >> 4) { // not sure this is actually possible... but just in case
                            goto next_world_seed;
                        }
                        if (!isViableStructurePos(c->type, &g, p.x, p.z, 0)) {
                            goto next_world_seed;
                        }
                        break;
                    }
                    case BIOME: {
                        if (getBiomeAt(&g, 1, c->x, 255, c->z) != c->type) {
                            goto next_world_seed;
                        }
                        break;
                    }
                    default: {
                        assert(false && "constraint type not implmented!");
                    }
                }
            }
            num_seeds++;
            seeds = (uint64_t *)realloc(seeds, sizeof(uint64_t) * num_seeds);
            seeds[num_seeds - 1] = world_seed;
next_world_seed:
            ;
        }
    }

    return (Seeds){.seeds=seeds, .size=num_seeds};
}

#define LENGTH(x) (sizeof(x) / sizeof(x[0]))

int main(void) {
    Constraint constraints[] = {
        STRUCTURE_CONSTRAINT(Ruined_Portal, 25960, -22040),
        STRUCTURE_CONSTRAINT(Desert_Pyramid, -12584, -7592),
        STRUCTURE_CONSTRAINT(Desert_Pyramid, -8136, -3336),
        STRUCTURE_CONSTRAINT(Desert_Pyramid, 728, -15768),
        STRUCTURE_CONSTRAINT(Desert_Pyramid, 5144, -16152),
        STRUCTURE_CONSTRAINT(Desert_Pyramid, 22840, -24520),
    };
    Constraints cons = (Constraints){.cons=constraints, .length=LENGTH(constraints)};
    parse_constraints(cons);

    // filewriter part
    // open files
    FILE *structure_file = fopen("structure_seeds.txt", "w");
    if (structure_file == NULL) {
        fprintf(stderr, "Error opening structure_seeds.txt!\n");
        return 1; // indicating an error
    }

    FILE *world_file = fopen("world_seeds.txt", "w");
    if (world_file == NULL) {
        fprintf(stderr, "Error opening world_seeds.txt!\n");
        fclose(structure_file); 
        return 1; // same as structure
    }

    Seeds structure_seeds = solve_constraints_for_structure_seeds(cons);
    printf("Found %llu structure seeds!\n", (unsigned long long)structure_seeds.size);
    // structure seeds to file
    for (size_t i = 0; i < structure_seeds.size; i++) {
        fprintf(structure_file, "%" PRIu64 "\n", structure_seeds.seeds[i]);
    }

    Seeds world_seeds = solve_constraints_for_world_seeds(cons, structure_seeds);
    printf("Found %llu world seeds!\n", (unsigned long long)world_seeds.size);
    // world seeds to file
    for (size_t i = 0; i < world_seeds.size; i++) {
        fprintf(world_file, "%" PRIu64 "\n", world_seeds.seeds[i]);
    }

    // close files
    fclose(structure_file);
    fclose(world_file);

    free(structure_seeds.seeds);
    free(world_seeds.seeds);

    return 0;
}
