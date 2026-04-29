`ifndef APB_DRIVER_BASE_SV
`define APB_DRIVER_BASE_SV

class apb_driver_base extends uvm_driver #(apb_seq_item);
    `uvm_component_utils(apb_driver_base)

    virtual apb_interface       vif;
    apb_seq_item                txn;
    uvm_active_passive_enum     agt_mode;

    function new ( string name = "apb_driver_base", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);

        if ( !uvm_config_db #(virtual apb_interface) :: get (this, "", "vif", vif) )
            `uvm_fatal("NOVIF", $sformatf("No interface set for %s.vif", get_full_name() ))

        if ( !uvm_config_db #(uvm_active_passive_enum) :: get (this, "", "agt_mode", agt_mode) )
            `uvm_fatal("NOAGTMODE", $sformatf("No agt_mode set for %s.agt_mode", get_full_name() ))
    endfunction
endclass

`endif
