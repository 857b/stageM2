#!/usr/bin/gawk -f

BEGIN {newl = 1 }
/^#/{next}
/^TAC>> .* :/{
	r = match($0, /:[[:blank:]]*([[:digit:]]*)[[:alpha:]]*$/, pats);
	if (newl) {
		printf ("%s", pats[1]);
		newl=0;
	} else {
		printf (" %s", pats[1]);
	}
	next
}
/Query-stats/{
	r = match($0, /succeeded in ([[:digit:]]*) milliseconds/, pats);
	printf (" %s", pats[1])
}
/^[[:blank:]]*$/{
	if (!newl) {
		printf("\n")
		newl = 1;
	}
}
