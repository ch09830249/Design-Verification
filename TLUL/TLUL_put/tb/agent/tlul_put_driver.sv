class tlul_put_driver extends uvm_driver #(tlul_transaction);
  virtual tlul_if vif;

  `uvm_component_utils(tlul_put_driver)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual tlul_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not set for tlul_put_driver");
  endfunction

  task run_phase(uvm_phase phase);
    tlul_transaction tr;
    #20;        // align rst_n in top
    forever begin
      seq_item_port.get_next_item(tr);
      `uvm_info(get_type_name(), "before put", UVM_MEDIUM)
      tr.print();
      drive_request(tr);
      get_response(tr);
      `uvm_info(get_type_name(), "before put", UVM_MEDIUM)
      tr.print();
      seq_item_port.item_done(tr);
    end
  endtask

  task drive_request(tlul_transaction tr);
    @(posedge vif.clk);

    // Set up request
    vif.a_valid   <= 1;
    vif.a_opcode  <= tr.opcode;
    vif.a_param   <= tr.param;
    vif.a_size    <= tr.size;
    vif.a_mask    <= tr.mask;
    vif.a_address <= tr.address;
    vif.a_data    <= tr.data;
    vif.a_source  <= tr.source;

    // Wait for handshake
    do @(posedge vif.clk); while (!vif.a_ready);
    vif.a_valid <= 0;

    `uvm_info(get_type_name(), $sformatf("Sent TLUL %s: addr=0x%08h data=0x%08h mask=0x%h source=0x%0h", 
               tr.is_get ? "GET" : "PUT", tr.address, tr.data, tr.mask, tr.source), UVM_MEDIUM)
  endtask

  task get_response(tlul_transaction tr);
    // Wait for response
    do @(posedge vif.clk); while (!vif.d_valid);
    vif.d_ready <= 1;
    @(posedge vif.clk);
    vif.d_ready <= 0;

    // Capture response
    tr.resp_opcode = vif.d_opcode;
    tr.resp_param  = vif.d_param;
    tr.resp_size   = vif.d_size;
    tr.resp_data   = vif.d_data;
    tr.resp_source = vif.d_source;
    tr.resp_sink   = vif.d_sink;

    `uvm_info(get_type_name(), $sformatf("Received Response: opcode=%0d data=0x%08h source=0x%0h", 
               tr.resp_opcode, tr.resp_data, tr.resp_source), UVM_MEDIUM)
  endtask
endclass

