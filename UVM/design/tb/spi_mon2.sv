class spi_mon2 extends uvm_monitor;
  `uvm_component_utils(spi_mon2)

  virtual spi_if.mon_mp vif;
  uvm_analysis_port #(spi_tran) mon2_ap;

  logic [7:0] slave_tx_data; 
  int mon2_tran_id_entire = 0; 
  int mon2_tran_id_bit = 0;

  function new(string name, uvm_component parent);
      super.new(name, parent);
      mon2_ap = new("mon2_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if.mon_mp)::get(this, "", "vif", vif)) begin
      `uvm_error("MON2", "Virtual interface not found in config db")
    end
    if(!uvm_config_db#(logic [7:0])::get(this, "", "slave_tx_data", slave_tx_data)) begin 
      `uvm_error("MON2", "Expected slave response not found in config db.")
    end 
    if (!uvm_config_db # (bit)::get(this, "", "mon1_abort", monitor1_abort)) begin
			`uvm_error("MON2", "Aborter variable not found in config db")
		end

  endfunction

  int lead_01 = 0; 
  int fall_01 = 0;
  int lead_00 = 0; 
  int lead_10 = 0; 
  int lead_11 = 0; 
  int fall_11 = 0;

  /*
  Negative monitor will attempt simulation of all 4 SPI types by adjusting:
  1. CPOL: clock signal inversion. 
  2. CPHA: clock phase adjustment (half period faster). 
  */
  task run_phase(uvm_phase phase);
    fork 
      // SPI1: no need for adjustments on clock, mosi sampled on leading-posedge, miso on trailing-negedge
      begin 
        spi_tran item;
        fork 
          forever begin
            @(posedge vif.sclk);
            item = spi_tran::type_id::create("item",this);
            item.mt = OL0HA1_L;
            item.tran_time_start = $time; 
            item.mosi = vif.mosi;
            item.curr_lead = lead_01++; 
            mon2_ap.write(item);
            `uvm_info("MON2", $sformatf("OL0HA1: leading posedge sample."), UVM_LOW);
          end          
          forever begin
            @(negedge vif.sclk);
            item = spi_tran::type_id::create("item",this);
            item.mt = OL0HA1_T;
            item.tran_time_start = $time; 
            item.miso = vif.miso;
            item.curr_fall = fall_01++; 
            mon2_ap.write(item);
            `uvm_info("MON2", $sformatf("OL0HA1: trailing negedge sample."), UVM_LOW);
          end
        join 
      end
      // SPI0: NOT CHANGING THE CLOCK, mosi and miso both sampled on leading-posedge.
      begin 
        spi_tran item;
        forever begin
            @(posedge vif.sclk);
            item = spi_tran::type_id::create("item",this);
            item.mt = OL0HA0;
            item.tran_time_start = $time; 
            item.mosi = vif.mosi;
            item.miso = vif.miso;
            item.curr_lead = lead_00++; 
            mon2_ap.write(item);
            `uvm_info("MON2", $sformatf("OL0HA0: leading posedge sample."), UVM_LOW);
          end
      end
      // SPI2: NOT CHANGING THE CLOCK, mosi sampled on falling edge, in this case moved to trailing edge and miso on rising edge, the leading edge. [will cause data mismatch]
      begin 
        spi_tran item;
        forever begin
          @(negedge vif.sclk);
          item = spi_tran::type_id::create("item",this);
          item.mt = OL1HA0;
          item.tran_time_start = $time; 
          item.mosi = vif.mosi;
          item.miso = vif.miso;
          item.curr_lead = lead_10++; 
          mon2_ap.write(item);
          `uvm_info("MON2", $sformatf("OL1HA0: leading negedge sample."), UVM_LOW);
        end
      end
      // SPI3: NOT CHANGING THE CLOCK, mosi and miso sampled both on the leading-negedge [will cause data mismatch]
      begin 
        spi_tran item;
        fork 
          forever begin
            @(negedge vif.sclk);
            item = spi_tran::type_id::create("item",this);
            item.mt = OL1HA1_L;
            item.tran_time_start = $time; 
            item.miso = vif.miso;
            item.curr_lead = lead_11++; 
            mon2_ap.write(item);
            `uvm_info("MON2", $sformatf("OL1HA1: leading negedge sample."), UVM_LOW);
          end          
          forever begin
            @(posedge vif.sclk);
            item = spi_tran::type_id::create("item",this);
            item.mt = OL1HA1_T;
            item.tran_time_start = $time; 
            item.mosi = vif.mosi;
            item.curr_fall = fall_11++; 
            mon2_ap.write(item);
            `uvm_info("MON2", $sformatf("OL1HA1: trailing posedge sample."), UVM_LOW);
          end
        join 
      end
    join
  endtask
endclass
