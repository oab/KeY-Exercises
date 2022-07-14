public class NodeCycle implements Cycle {
    NodeCycle next; 
    final int value;

    public NodeCycle(int value) {
	this.value = value;
	this.next = this;
    }

    private NodeCycle(int value, NodeCycle next) {
	this.value = value;
	this.next = next;
    }
    
    public NodeCycle next() {
	return next;
    }

 
    public Cycle add(int value) {
	NodeCycle added = new NodeCycle(value,this.next);
	this.next = added;
	return added;
    }


    public Cycle remove() {
	if(this.next == this) return this; 
	NodeCycle newLeftnext = this.next;
	NodeCycle left = this.next;
	while(left.next != this) left = left.next;
	left.next = newLeftnext;
	this.next = this;
	return newLeftnext;
	
    }

    public int size() {
	int size = 1;
	NodeCycle current= this;
	while (current.next() != this) size++;	
	return size;
    }

    public int value() {
	return this.value;
    }

    /*
    public String toString() {
	StringBuilder s = new StringBuilder();
	NodeCycle current = this;
	s.append("->");
	do {
	    s.append(Integer.toString(current.value()));
	    current = current.next();
	    s.append("->");	    
	} while (current != this);

	
	return s.toString();
    }
    */

    

}
