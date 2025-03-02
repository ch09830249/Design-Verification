// Create alias for parameterized "string" type mailbox
typedef mailbox #(string) s_mbox;

// Define a component to send messages
class comp1;

  	// Create a mailbox handle to put items
  	s_mbox 	names;

	// Define a task to put items into the mailbox
	task send ();
		for (int i = 0; i < 3; i++) begin
			string s = $sformatf ("name_%0d", i);
          #1 $display ("[%0t] Comp1: Put %s", $time, s);
			names.put(s);
		end
	endtask
endclass

// Define a second component to receive messages
class comp2;

	// Create a mailbox handle to receive items
	s_mbox 	list;


  	// Create a loop that continuously gets an item from
  	// the mailbox
	task receive ();
		forever begin
			string s;
			list.get(s);
          	$display ("[%0t]    Comp2: Got %s", $time, s);
		end
	endtask
endclass

// Connect both mailbox handles at a higher level
module tb;
  	// Declare a global mailbox and create both components
  	s_mbox 	m_mbx    = new();
  	comp1 	m_comp1  = new();
  	comp2 	m_comp2  = new();

  	initial begin
      // Assign both mailbox handles in components with the
      // global mailbox
      m_comp1.names = m_mbx;
      m_comp2.list = m_mbx;

      // Start both components, where comp1 keeps sending
      // and comp2 keeps receiving
      fork
      	m_comp1.send();
        m_comp2.receive();
      join
    end
endmodule

/*
	[1] Comp1: Put name_0
	[1]    Comp2: Got name_0
	[2] Comp1: Put name_1
	[2]    Comp2: Got name_1
	[3] Comp1: Put name_2
	[3]    Comp2: Got name_2
*/