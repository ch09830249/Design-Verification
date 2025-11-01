class axi_scoreboard extends uvm_component;
  `uvm_component_utils(axi_scoreboard)
  // uvm_analysis_export#(axi_txn) mon_export;


  function new(string name = "axi_scoreboard", uvm_component parent = null);
    super.new(name, parent);
    // mon_export = new("mon_export", this);
  endfunction


  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction


  task run_phase(uvm_phase phase);
    axi_txn tr;
    forever begin
      // mon_export.analysis_if.read(tr);
      // do simple check: just print events for now
      `uvm_info(get_type_name(), $sformatf("Scoreboard observed: %s", tr.convert2string()), UVM_LOW)
    end
  endtask


endclass
