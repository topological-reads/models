open util/graph[Resource]
open util/ternary
open topological_sort[Resource]

-- abstract sig ISBN {}
-- abstract sig DOI {}
-- abstract sig URL {}

-- abstract sig Author {}

abstract sig Resource {
	-- author: set Author
}

sig Book extends Resource {
	-- isbn: disj ISBN
}

sig Paper extends Resource {
	-- doi: disj DOI
}

sig Video extends Resource {
	-- url: disj URL
}

abstract sig ListMaintainer {
	lists: set ReadingList	
}

sig User extends ListMaintainer {
	follows: set ReadingList,
	read: set Resource,
	-- ratings: Resource -> lone Rating
}

sig Group extends ListMaintainer {
	users: set User
}

sig ReadingList {
	items: set Resource,
	order: Resource -> Resource
} {
	(dom[order] + ran[order]) in items
	dag[order]
}

fun groups[u: User]: set Group {
	u.~users
}

pred finished[u: User, r: ReadingList] {
	r.items in u.read
}

fun suggestedLists[u: User]: set ReadingList {
	{ r: u.groups.lists - u.lists | not u.finished[r] }
}

fun recommendations[u: User]: set Resource {
	{ item: u.follows.items - u.read | no item.~(u.follows.order) }
}

fact {
	all u: User | no u.recommendations implies no (u.follows.items - u.read)
}

enum Rating { OneStar, TwoStars, ThreeStars, FourStars, FiveStars }

run {
	/* Check that the following graph can be converted into a valid topologically
	 * sorted list.
	 *
	 *   A
	 *  / \
	 * B   C
	 *    / \  \  \
	 *   D   E  F  G
	 *  /
	 * H
	 */
	some graph, list: ReadingList, a, b, c, d, e, f, g, h: Resource {
		graph.items = list.items
		disj[a, b, c, d, e, f, g, h]
		b in graph.order[a]
		c in graph.order[a]
		d in graph.order[c]
		e in graph.order[c]
		f in graph.order[c]
		g in graph.order[c]
		h in graph.order[d]
		topological_sort[graph.order, list.order]
	}
} for 10 but exactly 2 ReadingList


