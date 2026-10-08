BEGIN;
CREATE SCHEMA IF NOT EXISTS "sym-ob-small";

CREATE TABLE IF NOT EXISTS "sym-ob-small"."graph" (
    id INTEGER PRIMARY KEY,
    graph_in_sparse6 TEXT NOT NULL UNIQUE,
    "order" INTEGER NOT NULL,
    "size" INTEGER NOT NULL,
    degree_sequence JSONB NOT NULL
);

CREATE TABLE IF NOT EXISTS "sym-ob-small"."clparameters" (
    id INTEGER PRIMARY KEY,
    software TEXT NOT NULL,
    version TEXT NOT NULL,
    prefix TEXT NOT NULL,
    suffix TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS "sym-ob-small"."canonicallabeling" (
    id INTEGER PRIMARY KEY,
    vertices_in_canonical_order JSONB NOT NULL,
    graph_in_sparse6_id INTEGER REFERENCES "sym-ob-small"."graph"(id),
    parameters_id INTEGER REFERENCES "sym-ob-small"."clparameters"(id)
);

CREATE TABLE IF NOT EXISTS "sym-ob-small"."maniplex" (
    id INTEGER PRIMARY KEY,
    "size" INTEGER NOT NULL,
    schlafli_symbol JSONB NOT NULL,
    generators JSONB NOT NULL,
    orientable BOOLEAN NOT NULL,
    polytopality TEXT NOT NULL CHECK (polytopality IN ('Polytopal', 'Faithful', 'Unfaithful')),
    cl_flag_graph_id INTEGER REFERENCES "sym-ob-small"."canonicallabeling"(id),
    cl_fg_edge_coloring TEXT,
    one_skeleton TEXT,
    cl_one_skeleton_id INTEGER REFERENCES "sym-ob-small"."canonicallabeling"(id),
    one_coskeleton TEXT,
    cl_one_coskeleton_id INTEGER REFERENCES "sym-ob-small"."canonicallabeling"(id),
    color_group JSONB NOT NULL,
    symmetry_type TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS "sym-ob-small"."graphexternalreference" (
    id INTEGER PRIMARY KEY,
    source TEXT NOT NULL,
    id_source TEXT NOT NULL,
    graph_id INTEGER REFERENCES "sym-ob-small"."graph"(id)
);

-- These three graph encodings are valid sparse6 strings. Their links to the
-- synthetic maniplexes below are only test relationships.
INSERT INTO "sym-ob-small"."graph"
    (id, graph_in_sparse6, "order", "size", degree_sequence)
VALUES
    (1, ':Bd', 3, 2, '[2,1,1]'::jsonb),
    (2, ':BcN', 3, 3, '[2,2,2]'::jsonb),
    (3, ':Cda', 4, 4, '[2,2,2,2]'::jsonb)
ON CONFLICT (id) DO NOTHING;

INSERT INTO "sym-ob-small"."clparameters"
    (id, software, version, prefix, suffix)
VALUES (1, 'toy-fixture', '1', '', '')
ON CONFLICT (id) DO NOTHING;

INSERT INTO "sym-ob-small"."canonicallabeling"
    (id, vertices_in_canonical_order, graph_in_sparse6_id, parameters_id)
VALUES
    (1, '[0,1,2]'::jsonb, 1, 1),
    (2, '[0,1,2]'::jsonb, 2, 1),
    (3, '[0,1,2,3]'::jsonb, 3, 1)
ON CONFLICT (id) DO NOTHING;

INSERT INTO "sym-ob-small"."maniplex" (
    id, "size", schlafli_symbol, generators, orientable, polytopality,
    cl_flag_graph_id, cl_fg_edge_coloring, one_skeleton, cl_one_skeleton_id,
    one_coskeleton, cl_one_coskeleton_id, color_group, symmetry_type
) VALUES
    (1, 24, '[4,8,8]'::jsonb, '[[1,0],[0,1],[1,0],[0,1]]'::jsonb,
     TRUE, 'Polytopal', 1, 'toy-colors', 'toy-skeleton', 2,
     'toy-coskeleton', 2, '[]'::jsonb, 'regular'),
    (2, 48, '[4,6,8]'::jsonb, '[[1,0],[1,0],[0,1],[0,1]]'::jsonb,
     FALSE, 'Faithful', 1, 'toy-colors', 'toy-skeleton', 3,
     NULL, NULL, '[[1,0]]'::jsonb, 'regular')
ON CONFLICT (id) DO NOTHING;

INSERT INTO "sym-ob-small"."graphexternalreference"
    (id, source, id_source, graph_id)
VALUES (1, 'Toy', 'toy-001', 1)
ON CONFLICT (id) DO NOTHING;

COMMIT;
