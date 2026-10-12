BEGIN;
CREATE SCHEMA IF NOT EXISTS "graphs-small";

CREATE TABLE IF NOT EXISTS "graphs-small"."graph" (
    graph6 TEXT PRIMARY KEY,
    num_vertices BIGINT NOT NULL,
    num_edges BIGINT NOT NULL,
    degree_sequence JSONB NOT NULL,
    min_degree BIGINT NOT NULL,
    max_degree BIGINT NOT NULL,
    is_regular BOOLEAN NOT NULL,
    num_components BIGINT NOT NULL,
    is_connected BOOLEAN NOT NULL,
    diameter BIGINT,
    radius BIGINT,
    girth BIGINT,
    is_tree BOOLEAN NOT NULL,
    is_forest BOOLEAN NOT NULL,
    is_bipartite BOOLEAN NOT NULL,
    is_planar BOOLEAN NOT NULL,
    is_eulerian BOOLEAN NOT NULL,
    num_triangles BIGINT NOT NULL,
    clique_number BIGINT NOT NULL,
    independence_number BIGINT NOT NULL,
    chromatic_number BIGINT NOT NULL,
    automorphism_count BIGINT NOT NULL
);

INSERT INTO "graphs-small"."graph" (
    graph6, num_vertices, num_edges, degree_sequence, min_degree, max_degree,
    is_regular, num_components, is_connected, diameter, radius, girth,
    is_tree, is_forest, is_bipartite, is_planar, is_eulerian, num_triangles,
    clique_number, independence_number, chromatic_number, automorphism_count
) VALUES
    ('B?', 3, 0, '[0,0,0]'::jsonb, 0, 0,
     TRUE, 3, FALSE, NULL, NULL, NULL,
     FALSE, TRUE, TRUE, TRUE, FALSE, 0,
     1, 3, 1, 6),
    ('BO', 3, 1, '[1,1,0]'::jsonb, 0, 1,
     FALSE, 2, FALSE, NULL, NULL, NULL,
     FALSE, TRUE, TRUE, TRUE, FALSE, 0,
     2, 2, 2, 2),
    ('BW', 3, 2, '[2,1,1]'::jsonb, 1, 2,
     FALSE, 1, TRUE, 2, 1, NULL,
     TRUE, TRUE, TRUE, TRUE, FALSE, 0,
     2, 2, 2, 2),
    ('Bw', 3, 3, '[2,2,2]'::jsonb, 2, 2,
     TRUE, 1, TRUE, 1, 1, 3,
     FALSE, FALSE, FALSE, TRUE, TRUE, 1,
     3, 1, 3, 6)
ON CONFLICT (graph6) DO NOTHING;

COMMIT;
