package unionfind;

public class Elements {

    private int[] elements;
    private final int size;
    
    protected Elements(int size) {
	this.elements = new int[2*size];
	this.size = size;
	for(int i=0;i<elements.length;i+=2) {
	    elements[i]=i/2;
	    elements[i+1]=1;
	    
	}
    }

    public int getSize() { return this.size; }
    
    public int getParent(final int i) {
	return elements[2*i];
    }

    public int setParent(final int i, final int v) {
 	return elements[2*i] = v;
    }

    public int getSize(final int i) {
      	return elements[2*i+1];
    }

    public int setSize(final int i, final int v) {
      	return elements[2*i+1] = v;
    }
    
    public int findRoot(final int i) {
	int e = i;
	int old = i;
	while((e = getParent(e)) != old) old = e;
	return e;
    }

    public void union(final int i,final int j) {
	
	int x = findRoot(i);
	int y = findRoot(j);
	
	if(x == y) return;	
	if(getSize(x) < getSize(y)) {
	    int temp = y;
	    y = x;
	    x = temp;
	}
	
	setParent(y,x);
	setSize(x,getSize(x) + getSize(y));
	
    }


}
