/*
    1. A function is meant to do some processing on the input and return a "single value", whereas  只能回傳一個值
       a task is more general and can calculate "multiple result values" and return them using output and inout type arguments. 可以回傳多個值

    2. Tasks can contain simulation time consuming elements such as @, posedge and others.  可以有 time-consuming 的字樣

    Syntax
      // Style 1
      task [name];
        input  [port_list];
        inout  [port_list];
        output [port_list];
        begin
          [statements]
        end
      endtask

      // Style 2
      task [name] (input [port_list], inout [port_list], output [port_list]);
        begin
          [statements]
        end
      endtask

      // Empty port list
      task [name] ();
        begin
          [statements]
        end
      endtask

    - Static task
      If a task is static, then all its member variables will be "shared across different invocations" of the same task that has been launched to run concurrently
    - Automatic task

*/

module tb;
  // task sum (input [7:0] a, b, output [7:0] c);
  //   begin
  //     c = a + b;
  //   end
	// endtask
  // or
	task sum;
		input  [7:0] a, b;
		output [7:0] c;
		begin
			c = a + b;
		end
	endtask

	initial begin
		reg [7:0] x=1, y=2, z=4;
		sum (x, y, z);
    $display("x=%0d, y=%0d, z=%0d", x, y, z);
	end
endmodule

/*
  x=1, y=2, z=3
*/