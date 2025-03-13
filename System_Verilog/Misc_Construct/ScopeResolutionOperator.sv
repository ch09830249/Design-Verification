/*
    The scope resolution operator :: is used to refer an identifier within the scope of a class.    
        before::after  =>  就是在 before 的範圍內找 after

    scope resolution operator ::
        Left hand side of the scope resolution operator :: 
            => "class type name", "package name", "covergroup type name", "coverpoint or cross name", "typedef name" 
    The right hand side of the operator 
            => "variable" or "method name"
*/

// Define extern function
class ABC;
	int 	data;

	extern virtual function void display();     // class 外部找 function display
endclass

// Definition of an external function using scope
// resolution operator
function void ABC::display();       // 其實用法和 C++ Namespace 很像    class name::function name
	$display("data = 0x%0h", data);
endfunction

module tb;
	initial begin
		ABC abc = new();
		abc.data = 32'hface_cafe;
		abc.display();
	end
endmodule

/*
    data = 0xfacecafe
    ncsim: *W,RNQUIE: Simulation is complete.
*/



// Access static function and method    Static function: 所有該 class 共同擁有的 method
class ABC;
	static int 	data;

	static function void display();
		$display("data = 0x%0h", data);
	endfunction
endclass

module tb;
	initial begin
      	ABC a1, a2;

      	// Assign to static variable before creating
      	// class objects, and display using class_type and
      	// scope resolution operator
		ABC::data = 32'hface_cafe;
		ABC::display();             // 直接用 class name 和 :: 去取用

      	a1 = new();
      	a2 = new();
      	$display ("a1.data=0x%0h a2.data=0x%0h", a1.data, a2.data);
	end
endmodule

/*
    data = 0xfacecafe
    a1.data=0xfacecafe a2.data=0xfacecafe
*/



// Using package        package 其實就是 C++ 的 namespace
package my_pkg;
	typedef enum bit {FALSE, TRUE} e_bool;
endpackage

module tb;
  bit val;

  initial begin
  	// Refer to types that have been declared
  	// in a package. Note that package has to
  	// be included in compilation but not
  	// necessarily "imported"
    val = my_pkg::TRUE;
    $display("val = 0x%0h", val);
  end
endmodule

/*
    val = 0x1
*/



//  Avoid namespace collision
package my_pkg;
	typedef enum bit {FALSE, TRUE} e_bool;
endpackage

import my_pkg::*;       // import 該 namespace

module tb;
  typedef enum bit {TRUE, FALSE} e_bool;

  initial begin
    e_bool val;

    // Be explicit and say that TRUE from my_pkg
    // should be assigned to val
    val = my_pkg::TRUE;         // 這裡引用 package 內的定義
    $display("val = 0x%0h", val);

    // TRUE from current scope will be assigned to
    // val
    val = TRUE;                 // 若沒指定, 則用該 scope 內定義的
    $display("val = 0x%0h", val);
  end
endmodule

/*
    val = 0x1
    val = 0x0
*/