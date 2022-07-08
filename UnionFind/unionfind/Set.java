// Originally made for experimentation with locset and reachability
// TODO: attempt to verify some properties on Element

// Regular union find without path compression
package unionfind;

import unionfind.Elements;
public class Set {

    
    private Elements elements;
    
    public Set(int size) {
	this.elements = new Elements(size);
    }

    // TODO: prove that this works
    public int[] sets() {
	int[] semisorted = new int[elements.getSize()];
	boolean[] seen = new boolean[elements.getSize()];

	int current = 0;
	int free = 0;

	while (current < elements.getSize()) {
	    while(current < elements.getSize() && seen[current]) {
		current++;
	    }
	    if(current == elements.getSize()) break;
	    
	    seen[current] = true;
	    int picked = elements.findRoot(current); //elements[current].findRoot().getName();
	    semisorted[free++] = current;
	    for(int i=current;i<elements.getSize();i++) {
		if(seen[i]) continue;

		if(picked == elements.findRoot(i)) {
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
	    int size = elements.getSize(elements.findRoot(sets[i])); //elements[sets[i]].findRoot().getSize();
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
	if(elements.getSize() < i || elements.getSize() < j) {
	    return;
	}
	    
	elements.union(i,j);

    }
    
    


}
