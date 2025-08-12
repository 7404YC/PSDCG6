class spi_mon0 extends uvm_monitor;
  `uvm_component_utils(spi_mon)
  uvm_analysis_port#(spi_tran) mon0_ap;
  virtual spi_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
	mon0_ap = new("mon0_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_error("MON0", "Virtual interspice not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    spi_tran item;
    forever begin
      // Trigger on vif.start
      @(negedge vif.start)
      // create item 
      item = spi_tran::type_id::create("in_item");
      // assign value
      item.rst_n = vif.rst_n;
      item.start = vif.start;
      item.tx_data = vif.tx_data;
      // write to analysis port for scb
      mon0_ap.write(item);
      // uvm_info
      `uvm_info("MON0", $sformatf("Observed input transaction: \nTX | RX\n0x%2h 0x%2h", item.tx_data, item.rx_data), UVM_LOW);
    end
  endtask
endclass

