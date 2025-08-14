class spi_mon1 extends uvm_monitor;
  `uvm_component_utils(spi_mon1)

  virtual spi_if.mon_mp vif;
  uvm_analysis_port #(spi_tran) mon1_ap;

  logic [7:0] slave_tx_data; 
  int mon1_tran_id_entire = 0; 
  int mon1_tran_id_bit = 0;

  function new(string name, uvm_component parent);
      super.new(name, parent);
      mon1_ap = new("mon1_ap", this);
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


  /*
  Monitors will collect 2 types of data, for mon 1 (output): 
  1. At done negedge collect for entire transaction final information. 
  2. At each sclk negedge collect for MISO information. (merge?)
  */
  task run_phase(uvm_phase phase);
    fork 
      begin 
        spi_tran tx;
        // Wait for busy to drop and done to go high
        bit prev_done = 0;
        forever begin
            @(vif.mon_cb);
            if (prev_done == 0 && vif.mon_cb.done == 1) begin
                tx = spi_tran::type_id::create("tx",this);
                tx.tran_id = mon1_tran_id_entire++;
                tx.mt = ENTIRE;
                tx.tran_time_end = $time; 
                tx.rx_data = vif.mon_cb.rx_data;
                tx.start = vif.mon_cb.start;
                tx.done = vif.mon_cb.done;
                mon1_ap.write(tx);
                `uvm_info("MON1", $sformatf("ENTIRE: Observed output transaction: 0x%02X on transaction ID: %d", tx.rx_data, tx.tran_id), UVM_LOW);
            end
            prev_done = vif.mon_cb.done;
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
	  tr = spi_tran::type_id::create("reset_tran");
	  tr.mt = BIT_RESET;
	  tr.tran_time_start = $time;
	  tr.rst_n = vif.rst_n;
	  tr.busy = vif.mon_cb.busy;
	  tr.cs_n = vif.cs_n;
	  tr.sclk = vif.sclk;
	  tr.mosi = vif.mosi;
 	  tr.tran_time_end = $time;
  	`uvm_info("MON1", $sformatf("RESET: rst_n=%0b, busy=%0b, cs_n=%0b, sclk=%0b, mosi=%0b", 
  	                              tr.rst_n, tr.busy, tr.cs_n, tr.sclk, tr.mosi), UVM_LOW);
	  mon1_ap.write(tr);
          monitor1_abort = 1'b1;
        end
      end
    join
  endtask
endclass
