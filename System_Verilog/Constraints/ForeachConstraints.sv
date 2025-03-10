class ABC;
  rand bit[3:0] array [5];    // 有指定 5 個元素, 每個元素 4 個 bits

  // This constraint will iterate through each of the 5 elements
  // in an array and set each element to the value of its
  // particular index
  constraint c_array { 
    foreach (array[i]) {
      array[i] == i;      // array 中每個值必須與 index 相同
    }
  }
endclass

module tb;
  initial begin
    ABC abc = new;
    abc.randomize();
    $display ("array = %p", abc.array);
  end
endmodule

/*
  array = '{'h0, 'h1, 'h2, 'h3, 'h4}
*/


// Dynamic Array/Queue
/*
  foreach loop cannot be directly used. Therefore, 
  the array's size has to be either assigned directly or constrained as part of the set of constraints.
*/
class ABC;
  rand bit[3:0] darray []; 		// Dynamic array -> size unknown
  rand bit[3:0] queue [$]; 		// Queue -> size unknown

  // Assign size for the queue if not already known
  constraint c_qsize  { queue.size() == 5; }      // 這裡要限制 size => queue 和 dynamic array size 是不確定的

  // Constrain each element of both the arrays
  constraint c_array  { 
    foreach (darray[i])
      darray[i] == i;
    foreach (queue[i])
      queue[i] == i + 1;    // value == index+1
  }
  // Size of an array can be assigned using a constraint like
  // we have done for the queue, but let's assign the size before
  // calling randomization
  function new ();
		darray = new[5]; 	// Assign size of dynamic array     // dynamic array 例化時, 指定 size
	endfunction
endclass

module tb;

  initial begin
    ABC abc = new;
    abc.randomize();
    $display ("array = %p
queue = %p", abc.darray, abc.queue);
  end
endmodule

/*
  array = '{'h0, 'h1, 'h2, 'h3, 'h4}
  queue = '{'h1, 'h2, 'h3, 'h4, 'h5}
*/


// Multidimensional Array
// a multidimensional static array with a "packed" structure.
class ABC;
  rand bit[4:0][3:0] md_array [2][5]; 	// Multidimansional Arrays    4*5=20 bits
  constraint c_md_array {
    foreach (md_array[i]) {
    	foreach (md_array[i][j]) {
        foreach (md_array[i][j][k]) {
          if (k%2 == 0)
            md_array[i][j][k] == 'hF; // k 為偶數的話, 值為 F
          else
            md_array[i][j][k] == 0;
        }
      }
    }
  }
endclass

module tb;
  initial begin
    ABC abc = new;
    abc.randomize();
    $display ("md_array = %p", abc.md_array);
  end
endmodule

/*
  md_array = '{'{'hf0f0f, 'hf0f0f, 'hf0f0f, 'hf0f0f, 'hf0f0f}, '{'hf0f0f, 'hf0f0f, 'hf0f0f, 'hf0f0f, 'hf0f0f}}
*/


class ABC;
  rand bit[3:0] md_array [][]; 	// Multidimansional Arrays with unknown size

  constraint c_md_array {
     // First assign the size of the first dimension of md_array
     md_array.size() == 2;
     // Then for each sub-array in the first dimension do the following:
     foreach (md_array[i]) {
        // Randomize size of the sub-array to a value within the range
        md_array[i].size() inside {[1:5]};      // 可以 random 一個 size
        // Iterate over the second dimension
        foreach (md_array[i][j]) {

           // Assign constraints for values to the second dimension
           md_array[i][j] inside {[1:10]};
         }
      }
   }

endclass

module tb;
  initial begin
    ABC abc = new;
    abc.randomize();
    $display ("md_array = %p", abc.md_array);
  end
endmodule


/*
  md_array = '{'{'h9, 'h6, 'h7, 'h9, 'h1}, '{'h5, 'h9, 'h4, 'h2}}
*/




//Array Reduction
class ABC;
  rand bit[3:0] array [5];
  // Intrepreted as int'(array[0]) + int'(array[1]) + .. + int'(array[4]) == 20;
  constraint c_sum { array.sum() with (int'(item)) == 20; }   // array 所有元素加起來要等於 20
endclass

module tb;
  initial begin
    ABC abc = new;
    abc.randomize();
    $display ("array = %p", abc.array);
  end
endmodule

/*
  array = '{'h4, 'h2, 'h2, 'h4, 'h8}
*/