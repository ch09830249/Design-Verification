/*
Tasks that are declared outside all modules are called global tasks as they have a global scope and can be called within any module.
If the task was declared within the module des , it would have to be called in reference to the module instance name.
*/

// This task is outside all modules
// task display();
//   $display("Hello World !");
// endtask

// module des;
//   initial begin
//     display();
//   end
// endmodule

module tb;
	des u0();

	initial begin
		u0.display();  // Task is not visible in the module 'tb'
	end
endmodule

module des;
	initial begin
		display(); 	// Task definition is local to the module
	end

	task display();
		$display("Hello World");
	endtask
endmodule

/*
Hello World
Hello World   
*/