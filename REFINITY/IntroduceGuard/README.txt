A refactoring that eases the reading of the control flow.

---- BEFORE -----|---- AFTER ------
if(cond1) {	 |if(!cond1) {	 
 <computation 1> | <signal error 1>
} else {	 |}		 
 <signal error 1>|<computation 1> 		 
}		 |	 
-----------------|-----------------

This becomes more apparant in deeply nested cases
wher we can apply the refactoring several times.

---- BEFORE -------|---- After -------
if(cond1) {	   |if(!cond1) {	   
 <computation 1>   | <signal error 1>
 if(cond2) {       | return;       
   <computation 2> |} 
 } else {          |if(!cond2)          
   <signal error 2>| <signal error 2>
 }                 | return;                 
} else {	   |}	   
 <signal error 1>  | <computation 1>  
}		   | <computation 2>		   	 
		   |		   
-------------------|-------------------








