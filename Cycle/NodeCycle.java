public class NodeCycle implements Cycle {
    NodeCycle next = this; 
    final int value;
    
    public NodeCycle(int value) {
	this.value = value;
    }

    public Cycle next() {
	return next;
    }

    public void remove() {
	//unimplemented
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

    

}
