class spi_mon0 extends uvm_monitor;
  `uvm_component_utils(spi_mon0)
  uvm_analysis_port#(spi_tran) mon0_ap;
  virtual spi_if.mon_mp vif;

  int mon0_tran_id_entire = 0; 
  int mon0_tran_id_bit = 0; 

  function new(string name, uvm_component parent);
    super.new(name, parent);
	mon0_ap = new("mon0_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if.mon_mp)::get(this, "", "vif", vif)) begin
      `uvm_error("MON0", "Virtual interspice not found in config db")
    end
  endfunction

  /*
  Monitors will collect 2 types of data, for mon 0 (input): 
  1. At start negedge collect for entire transaction initial information. 
  2. At each sclk posedge collect for MOSI information. (merge?)
  */
  task run_phase(uvm_phase phase);
    fork
      begin // entire transaction
        spi_tran item;
        forever begin
          // Trigger on vif.start
          @(posedge vif.mon_cb.start)
          #1;
          // create item 
          item = spi_tran::type_id::create("in_item_t1");
          // assign value
          item.tran_id = mon0_tran_id_entire++;
          item.mt = ENTIRE;
          item.tran_time_start = $time; 
          item.rst_n =		vif.rst_n;
          item.start =		vif.mon_cb.start;
          item.tx_data =	vif.mon_cb.tx_data;
          item.mosi =		vif.mosi;
          item.cs_n =		vif.cs_n;
          item.miso =		vif.miso;
          item.busy =		vif.mon_cb.busy;
          item.done =		vif.mon_cb.done;
          // write to analysis port for scb
          mon0_ap.write(item);
          // uvm_info
          `uvm_info("MON0", $sformatf("ENTIRE: Observed input transaction: \nTX | RX\n0x%2h 0x%2h ", item.tx_data, item.rx_data), UVM_LOW);
        end
      end
      begin // MOSI collection 
        spi_tran item; 
        int curr_index; 
        forever begin 
          item = spi_tran::type_id::create("in_item_t2");
          item.tran_id = mon0_tran_id_bit++;
          item.mt = BIT_MOSI; 
          item.tran_time_start = $time;
          curr_index = 0;
          repeat(8) begin 
            @(posedge vif.sclk) // TODO: using the mon_cb here is really ticking me off
            #1;
            item.MS_data[7- ((curr_index++) % 8)] = vif.mosi;
          end 
          @(posedge vif.mon_cb.done) // Part of T024
          #1; 
          item.tx_data = vif.mon_cb.tx_data;
          item.tran_time_end = $time;
          `uvm_info("MON0", $sformatf("BIT: Observed mosi details: %8b on transaction ID: %d", item.MS_data, item.tran_id), UVM_LOW);
          mon0_ap.write(item);
        end 
      end
    join
  endtask
endclass

