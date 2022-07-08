// Originally made for experimentation with locset and reachability
// TODO: attempt to verify some properties on Element

// Regular union find without path compression
class Set {

    class Element {

	Element parent;
	final int name;
	int size;
	
	
	Element(int name) {
	    this.parent = this;
	    this.name = name;
	    this.size = 1;
	}

	Element findRoot() {
	    Element node = this;
	    while(node.parent != node) {
		node = node.parent;
	    }
	    return node;
	}
	
    }


    Element[] elements;
    
    
    public Set(int size) {
	this.elements = new Element[size];
	for(int i=0;i<elements.length;i++) {
	    elements[i] = new Element(i);
	}
    }
    public int size(int i) {
	return elements[i].findRoot().size;
    }

    // TODO: prove that this works
    public int[] sets() {
	int[] semisorted = new int[elements.length];
	boolean[] seen = new boolean[elements.length];

	int current = 0;
	int free = 0;
	while (current < elements.length) {
	    while(current < elements.length && seen[current]) {
		current++;
	    }
	    if(current == elements.length) break;
	    
	    seen[current] = true;
	    int picked = elements[current].findRoot().name;
	    semisorted[free++] = current;
	    
	    for(int i=current;i<elements.length;i++) {
		if(seen[i]) continue;
		if(picked == elements[i].findRoot().name) {
		    seen[i] = true;
		    semisorted[free++] = i;
		}
	    }

	   
	}
	return semisorted;
    }
	
    
    @Override
    public String toString() {
	int[] sets = this.sets();
	if(sets.length == 0) return "";
	StringBuilder s = new StringBuilder();
	int i = 0;
	while(i<sets.length) {
	    int size = elements[sets[i]].findRoot().size;
	    s.append('{');
	    while(0 < size) {
		size--;
		s.append(Integer.toString(sets[i]));
		i++;
		if(0 < size) {
		    s.append(',');
		}
	    }
	    s.append('}');
	    if(0 < size) {	
		s.append(',');
	    }
	    
	    

	}

	return s.toString();
    }
    
	
    public void union(int i, int j) {
	if(elements.length < i || elements.length < j) {
	    return;
	}
	    
	Element x = elements[i].findRoot();
	Element y = elements[j].findRoot();

	if(x == y) {
	    return;
	}

	if(x.size < y.size) {
	    Element temp = y;
	    y = x;
	    x = temp;
	}

	y.parent = x;
	x.size += y.size;

    }
    
    


}
