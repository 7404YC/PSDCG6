class spi_mon1 extends uvm_monitor;
    `uvm_component_utils(spi_mon1)

    virtual spi_if.mon_mp vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_error("MONITOR", "Virtual interspice not found in config db")
    end
  endfunction

    // Run phase logic that observes and sends transaction
    task run_phase(uvm_phase phase);
        // Wait for busy to drop and done to go high
        bit prev_done = 0;
        forever begin
            @(posedge vif.clk);
            if (prev_done == 0 && vif.mon_cb.done == 1) begin
                spi_tran tx = spi_tran::type_id::create("tx",this);
                tx.rx_data = vif.mon_cb.rx_data;
                mon1_ap.write(tx);
                `uvm_info("MON1", $sformatf("Observed transaction: 0x%02X", tx.rx_data), UVM_LOW);
            end
            prev_done = vif.mon_cb.done;
        end
    endtask

endclass
