module topological_sort [T]

open util/graph[T]

fun vertices[g: T -> T]: set T {
	dom[g] + ran[g]
}

/**
 * Determine whether or not a given sort is a valid topological sort for a
 * graph.
 */
pred topological_sort[graph: T -> T, sort: T -> T] {
	/* Topological sorts only exist for acyclic graphs */
	dag[graph]

	/* The sort has a single first element */
	tree[sort]
	let vs = vertices[graph] {
		/* Every vertex appears at most once in the sequence */
		functional[sort,  vs] -- lone v->
		functional[~sort, vs] -- lone ->v
	}

	/* A prerequisite must always be completed before anything which depends on
	 * it. Since the graph is assumed to provide a prerequisite graph, we enforce
	 * that prerequisites always appear before dependents in the sequence.
	 */
	all t1, t2: T | t2 in t1.^graph implies t2 in t1.^sort
}
