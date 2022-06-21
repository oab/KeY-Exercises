class Bijection {

    static int product(int a[]) {
	int p = 1;
	for(int i=0;i<a.length;i++) p *= a[i];
	return p;
    }

   static int[] iota(int n) {
	int[] out = new int[n];
	for(int i=0;i<n;i++) out[i] = i;
	return out;
	
    }
    
    static boolean succ(int[] index, int[] shape)  {
        end:{
	    for(int i=0;i<index.length;i++) {
		if(index[i] != shape[i]-1) break end;
		
	    }
	    return false;
	}

	int i = shape.length-1;
	boolean carry = shape[i] <= ++index[i];
	
	while(carry) {
	    index[i] = 0;
	    carry = shape[i] <= ++index[--i];
	}
	return true;
    }

    static  int[][] indices(int[] shape) {
    	int[][] out = new int[product(shape)][shape.length];
        int[] index = new int[shape.length];
	int i = 0;
	do {
	    out[i++] = Arrays.copyOf(index,index.length);	    
	} while (succ(index,shape));
	return out;
    }


    interface Layout {
	int flatten(int[] index, int shape[]);
    }
    
    static final Layout row_major_layout = new Layout() {
	    public int flatten(int[] index, int shape[]) {
		int x = 0;
		for(int i=0; i<index.length; i++) {
		    x *= shape[i];
		    x += index[i];
		}
		return x;
	    }
	};


    /* Definition 1. Let iota(N) = {0,...,N-1}
     * Definition 2. Let indices(shape) = iota(shape_0)*...*iota(shape_(n-1))
     *
     * The specification I used once to check for bijections is
     * given a bijective function f_(shape): indices(shape) -> iota(product(shape))
     *
     * The row_major_layout given above can be regarded as implementing all f_(shape)
     * such that ordering given is row major.
     *
     * 
     */

    static boolean bijection(Layout layout, int[] shape) {

	int[] flat = new int[product(shape)];	    
	int[][] indices = indices(shape);
	
	for(int i=0;i<indices.length;i++) {
	    flat[layout.flatten(indices[i],shape)]++;
	}


	for(int i=0;i<product(shape);i++) {
	    if(flat[layout.flatten(indices[i],shape)] != 1) {
		return false;
	    }
	}

	return true;

	


	
    }


}
