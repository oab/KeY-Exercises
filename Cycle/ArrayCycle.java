public class ArrayCycle implements Cycle {
    private final ArrayListInt items;
    private final int start;

    public ArrayCycle(int value) {
	this.items = new ArrayListInt();
	this.items.insert(0,value);
	this.start = 0;
    }

    private ArrayCycle(ArrayCycle left) {
	this.items = left.items;
	this.start = (left.start+1)%left.size();
    }

    public ArrayCycle next() {
	return new ArrayCycle(this);
    }

    public Cycle add(int value) {
	items.insert(start+1,value);
	return this.next();
    }

    public Cycle remove() {
	int value = items.remove(start);
	return new ArrayCycle(value);
    }

    public int size() {
	return items.size();
    }


    public int value() {
	return items.get(start);
    }

    /*
   public String toString() {
	StringBuilder s = new StringBuilder();
	s.append("->");
	int i = start;
	do {	    
	    s.append(Integer.toString(items.get(i)));
	    i = (i+1) % items.size();
	    s.append("->");	    
	} while(i != start);
	

	return s.toString();
    }
    */
 
    

}
