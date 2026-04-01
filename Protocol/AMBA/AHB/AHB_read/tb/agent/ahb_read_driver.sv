class ahb_read_driver extends uvm_driver #(ahb_transaction);
  `uvm_component_utils(ahb_read_driver)

  virtual ahb_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not set")
  endfunction

  virtual task run_phase(uvm_phase phase);
    ahb_transaction tr;
    forever begin
      seq_item_port.get_next_item(tr);
      tr.print();
      drive_read(tr);
      seq_item_port.item_done();
    end
  endtask

  task drive_read(ahb_transaction tr);
    wait (vif.HRESETn == 1);
    @(vif.cb);
    vif.cb.HTRANS <= 2'b10;
    vif.cb.HWRITE <= 0;
    vif.cb.HADDR  <= tr.addr;
    vif.cb.HSIZE  <= tr.size;
    vif.cb.HWDATA <= 0;

    do @(vif.cb); while (!vif.cb.HREADY);

    tr.data = vif.cb.HRDATA;

    @(vif.cb);
    vif.cb.HTRANS <= 2'b00;
    vif.cb.HADDR  <= 0;
    vif.cb.HSIZE  <= 3'b000;
  endtask

endclass
