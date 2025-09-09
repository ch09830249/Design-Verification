class ahb_write_sequence extends uvm_sequence #(ahb_transaction);
  `uvm_object_utils(ahb_write_sequence)

  function new(string name = "ahb_write_sequence");
    super.new(name);
  endfunction

  task body();
    ahb_transaction tr;
    repeat (3) begin
      tr = ahb_transaction::type_id::create("tr");
      tr.randomize() with { tr.addr[1:0] == 2'b00; tr.size == 3'b010; }; // Word aligned
      start_item(tr);
      finish_item(tr);
    end
  endtask
endclass
