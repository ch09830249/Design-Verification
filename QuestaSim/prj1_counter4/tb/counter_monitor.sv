`include "uvm_macros.svh"
import uvm_pkg::*;

class counter_monitor extends uvm_monitor;
  virtual counter_if vif;
  uvm_analysis_port #(counter_seq_item) ap;

  `uvm_component_utils(counter_monitor)

  function new(string name="counter_monitor", uvm_component parent=null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  task run_phase(uvm_phase phase);
    counter_seq_item item;
    forever begin
      @(posedge vif.clk);
      item = counter_seq_item::type_id::create("item");
      item.en = vif.en;
      ap.write(item);
    end
  endtask
endclass