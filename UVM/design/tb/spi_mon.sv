class spi_mon extends uvm_monitor;
  `uvm_component_utils(spi_mon)

  virtual spi_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_error("MONITOR", "Virtual interspice not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
    end
  endtask
endclass

