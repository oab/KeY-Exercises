public class ArrayListInt {
    int[] items;
    int used;

    private void resize() {
	this.items = java.util.Arrays.copyOf(items,items.length*2);  
    }
    
    public ArrayListInt() {
	this.items = new int[16];
	this.used = 0;
    }

    public int size() {
	return used;
    }

    public int get(int i) {
	return items[i];
    }


    public void insert(final int i, final int v) {
	if(used == items.length) resize();
       
	    
	for(int free = used; i < free; free--) {
	    items[free] = items[free-1];
	}
        used++;
	items[i] = v;	
    }
   
    public int remove(final int i) {
	final int value = items[0];
	for(int free = used; free < i; free--) {
	    items[free] = items[free-1];
	}
	this.used--;
	return value;
	

    }
    
    public String toString() {
	StringBuilder s = new StringBuilder();
	s.append('[');
	for(int i=0;i < used; i++) {
	    s.append(Integer.toString(items[i]));
	    if(i+1 != used) s.append(',');
	}
	
	s.append(']');
	return s.toString();
    }
    

    
    
    

}
