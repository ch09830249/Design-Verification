`include "uvm_macros.svh"
import uvm_pkg::*;

class counter_driver extends uvm_driver #(counter_seq_item);
  virtual counter_if vif;

  `uvm_component_utils(counter_driver)

  function new(string name="counter_driver", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    counter_seq_item req;
    forever begin
      seq_item_port.get_next_item(req);
      vif.en <= req.en;
      @(posedge vif.clk);
      seq_item_port.item_done();
    end
  endtask
endclass