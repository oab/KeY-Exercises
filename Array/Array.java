public class Array {
    private int[] value;
    private int[] shape;
    private int offset;

    /*@ model \seq seqvalue
      @ reresents seqvalue = \dl_array2seq(value);
      @*/

    /*@ model \seq seqshape
      @ reresents seqshape = \dl_array2seq(shape);
      @*/

    private Array(int[] value, int[] shape, int offset) {
	this.value = value;
	this.shape = shape;
	this.offset = offset;
    }

    private static int product(int a[]) {
	int p = 1;
	for(int i=0;i<a.length;i++) p *= a[i];
	return p;
    }

    public static Array scalar(int s) {
	return new Array(new int[]{s},new int[]{},0);
    }

    public static Array vector(int... v) {
	return new Array(Arrays.copyOf(v,v.length),new int[]{v.length},0);
    }

    public void reshape(int... shape) {
	if(product(this.shape) == product(shape)){
	    this.shape = shape;
	}
    }

 
    /*@ pure @*/ public int[] getShape() { return shape; }
    /*@ pure @*/ public int[] getValue() { return Arrays.copyOfRange(value,offset,offset+product(shape)); }
    /*@ pure @*/ public int dimensions() { return shape.length; }

    // debug method that leaks implementation, remove
    /*@ pure @*/ public int offset() { return offset; }


    /*@
      @ public static model boolean inBounds(int[] index, int[] shape) {
      @   return index.length <= shape.length &&
      @          (\forall int i; 0 <= i && i < index.length;
      @             0 <= index[i] && index[i] < shape[i]);
      @ }
      @*/

    // the fundamental MoA invariant: (i,j) psi A == j psi (i psi A)
    // This got quite ugly...

     
    /*@
      @ public invariant (\forall int[] index; inBounds(index,shape);
      @                   (\forall int[] left;;
      @                    (\forall int[] right;;  
      @                    \dl_array2seq(index) == \seqConcat( \dl_array2seq(left), \dl_array2seq(right) )
      @                    ==>  this.index(index).getValues() == this.index(left).index(right).getValues() )))
      @*/

    /*@
      @ public normal_behavior
      @ requires inBounds(index,shape);
      @*/
    public Array index(int... index) {
	return new Array(this.value,
			 Arrays.copyOfRange(shape, index.length, this.shape.length),
			 row_major(Arrays.copyOf(index,this.shape.length),this.shape));
    }
    
    static /*@ pure @*/ int row_major(int[] index, int shape[]) {
   	int x = 0;
   	for(int i=0; i<index.length; i++) {
    	    x *= shape[i];
    	    x += index[i];
    	}
    	return x;
    }
}
