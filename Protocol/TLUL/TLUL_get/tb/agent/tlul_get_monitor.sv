class tlul_get_monitor extends uvm_monitor;
  `uvm_component_utils(tlul_get_monitor)
  virtual tlul_if vif;
  uvm_analysis_port#(tlul_transaction) ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual tlul_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not set for tlul_get_monitor");
  endfunction

  virtual task run_phase(uvm_phase phase);
    tlul_transaction tr;
    forever begin
      @(posedge vif.clk);
      // Record A channel
      if (vif.a_valid && vif.a_ready) begin
        tr = tlul_transaction::type_id::create("tr");
        tr.opcode   = vif.a_opcode;
        tr.param    = vif.a_param;
        tr.size     = vif.a_size;
        tr.mask     = vif.a_mask;
        tr.address  = vif.a_address;
        tr.data     = vif.a_data;
        tr.source   = vif.a_source;
        tr.is_get   = (vif.a_opcode == 4);
        `uvm_info(get_type_name(), "Record A channel", UVM_MEDIUM)
        tr.print();
        ap.write(tr);
      end
      // Record D channel
      if (vif.d_valid && vif.d_ready) begin
        tr = tlul_transaction::type_id::create("tr");
        tr.resp_opcode = vif.d_opcode;
        tr.resp_param  = vif.d_param;
        tr.resp_size   = vif.d_size;
        tr.resp_data   = vif.d_data;
        tr.resp_source = vif.d_source;
        tr.resp_sink   = vif.d_sink;
        `uvm_info(get_type_name(), "Record D channel", UVM_MEDIUM)
        tr.print();
        ap.write(tr);
      end
    end
  endtask
endclass
