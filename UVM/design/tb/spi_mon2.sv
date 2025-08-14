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
      `uvm_error("MON1", "Virtual interface not found in config db")
    end
    if(!uvm_config_db#(logic [7:0])::get(this, "", "slave_tx_data", slave_tx_data)) begin 
      `uvm_error("MON1", "Expected slave response not found in config db.")
    end 
    if (!uvm_config_db # (bit)::get(this, "", "mon1_abort", monitor1_abort)) begin
			`uvm_error("MON0", "Aborter variable not found in config db")
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
      // SPI1: no need for adjustments on clock
      begin 
        spi_tran item;
        fork 
          forever begin
            @(posedge vif.sclk);
            item = spi_tran::type_id::create("item",this);
            item.mt = OL0HA1;
            item.tran_time_start = $time; 
            item.mosi = vif.mosi;
            item.curr_lead = lead_01++; 
            mon2_ap.write(item);
            `uvm_info("MON2", $sformatf("OL0HA1: leading edge sample."), UVM_LOW);
          end          
          forever begin
            @(negedge vif.sclk);
            item = spi_tran::type_id::create("item",this);
            item.mt = OL0HA1;
            item.tran_time_start = $time; 
            item.mosi = vif.mosi;
            item.curr_fall = fall_01++; 
            mon2_ap.write(item);
            `uvm_info("MON2", $sformatf("OL0HA1: falling edge sample."), UVM_LOW);
          end
        join 
      end
      // SPI0: NOT CHANGING THE CLOCK, mosi is sampled on simulated leading (negedge)
      begin 

      end
      begin 
        spi_tran tx;
        // Wait for busy to drop and done to go high
        bit prev_done = 0;
        forever begin
            @(vif.clk);
            if (prev_done == 0 && vif.done == 1) begin
                tx = spi_tran::type_id::create("tx",this);
                tx.tran_id = mon1_tran_id_entire++;
                tx.mt = ENTIRE;
                tx.tran_time_end = $time; 
                tx.rx_data = vif.rx_data;
                tx.start = vif.start;
                tx.done = vif.done;
                mon1_ap.write(tx);
                `uvm_info("MON1", $sformatf("ENTIRE: Observed output transaction: 0x%02X on transaction ID: %d", tx.rx_data, tx.tran_id), UVM_LOW);
            end
            prev_done = vif.done;
        end
      end
      begin   
        forever begin 
          spi_tran item;
          int curr_index;
          forever begin 
            #1; // black magic
            item = spi_tran::type_id::create("in_item_t2");
            item.tran_id = mon1_tran_id_bit++;
            item.tran_time_start = $time;
            item.mt = BIT_MISO;
            curr_index = 0;
            repeat(8) begin 
              if (monitor1_abort) begin 
                break;
              end 
              @(negedge vif.sclk) // TODO: using the mon_cb here is really ticking me off
              item.MS_data[7 - ((curr_index++) % 8)] = vif.miso;
            end 
            if (monitor1_abort) begin 
              monitor1_abort = 0;
              continue;
            end
            item.tran_time_end = $time; 
            `uvm_info("MON1", $sformatf("BIT: Observed miso details: %8b on transaction ID: %d", item.MS_data, item.tran_id), UVM_LOW);
            mon1_ap.write(item);  
          end 
        end
      end
      begin 
        forever begin 
          spi_tran tr;
          @(negedge vif.rst_n)
          monitor1_abort = 1'b1;
          #1;
	  tr = spi_tran::type_id::create("reset_tran");
	  tr.mt = BIT_RESET;
	  tr.tran_time_start = $time;
	  tr.rst_n = vif.rst_n;
	  tr.busy = vif.busy;
	  tr.cs_n = vif.cs_n;
	  tr.sclk = vif.sclk;
	  tr.mosi = vif.mosi;
 	  tr.tran_time_end = $time;
  	`uvm_info("MON1", $sformatf("RESET: rst_n=%0b, busy=%0b, cs_n=%0b, sclk=%0b, mosi=%0b", 
  	                              tr.rst_n, tr.busy, tr.cs_n, tr.sclk, tr.mosi), UVM_LOW);
	  mon1_ap.write(tr);
        end
      end
    join
  endtask
endclass
