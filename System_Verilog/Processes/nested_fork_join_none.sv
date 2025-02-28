module tb;
	initial begin
    $display ("[%0t] Main Thread: Fork join going to start", $time);
		fork
      // Thread1
      begin
			  fork
          // Thread1_0
          print (20, "Thread1_0");
          // Thread1_1
          print (30, "Thread1_1");
        join_none
        $display("[%0t] Nested fork has finished", $time);
      end
      // Thread2
      print (10, "Thread2");
    join_none
    $display ("[%0t] Main Thread: Fork join has finished", $time);
	end

  // Note that we need automatic task
  /*
    Without automatic keyword, the same display task with different string tags will produce the same display message. 
    This is because multiple threads call the same task and share the same variable in tool simulation memory. 
    In order for different threads to initiate different copies of the same task, automatic keyword has to be used.
  */
  task automatic print (int _time, string t_name);
    #(_time) $display ("[%0t] %s", $time, t_name);
  endtask
endmodule

/*
  [0] Main Thread: Fork join going to start
  [0] Main Thread: Fork join has finished
  [0] Nested fork has finished
  [10] Thread2
  [20] Thread1_0
  [30] Thread1_1
*/