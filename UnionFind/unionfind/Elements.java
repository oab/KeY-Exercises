package unionfind;

public final class Elements {

    private int[] elements;
    private final int size;
    
    protected Elements(int size) {
	this.elements = new int[2*size];
	this.size = size;
	for(int i=0,j=0;i<elements.length;i+=2,j++) {
	    elements[i]=j;
	    elements[i+1]=1;
	    
	}
    }

    protected int getSize() { return this.size; }
    
    protected int getParent(final int i) {
	return elements[2*i];
    }

    protected int setParent(final int i, final int v) {
 	return elements[2*i] = v;
    }

    protected int getSize(final int i) {
      	return elements[2*i+1];
    }

    protected int setSize(final int i, final int v) {
      	return elements[2*i+1] = v;
    }
    
    protected int findRoot(final int i) {
	int e = i;
	int old = i;
	while((e = getParent(e)) != old) {
	    old = e;
	}

	return e;
    }

    protected int findRootAndCompress(final int i) {
	int e = i;
	int old = i;
	while((e = getParent(e)) != old) {
	    setParent(old,-1);
	    old = e;
	}

	int esize = getSize(e);
	for(int j=0;j<size;j++) {
	    if(getParent(j) < 0) {
		setParent(j,e);
		setSize(j,esize);
	    }

	}
	return e;
    }


    protected void union(final int i,final int j) {
	
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
