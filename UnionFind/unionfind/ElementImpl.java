package unionfind;
import unionfind.Element;

class ElementImpl implements Element {
    
    ElementImpl parent;
    final int name;
    int size;

    public int getName() { return name; }
    public int getSize() { return size; }
   
    ElementImpl(int name) {
	this.parent = this;
	this.name = name;
	this.size = 1;
    }
    
    public ElementImpl findRoot() {
	ElementImpl e = this;
	ElementImpl old = this;
	while((e = e.parent) != old) old = e;
	return e;
    }
    
    public void union(ElementImpl other) {
	
	ElementImpl x = this.findRoot();
	ElementImpl y = other.findRoot();
	
	if(x == y) {
	    return;
	}
	
	if(x.size < y.size) {
	    ElementImpl temp = y;
	    y = x;
	    x = temp;
	}
	
	y.parent = x;
	x.size +=  y.size;
	
    }
}
