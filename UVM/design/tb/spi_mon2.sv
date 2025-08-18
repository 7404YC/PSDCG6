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
  int fall_00 = 0; 
  int lead_10 = 0; 
  int fall_10 = 0; 
  int lead_11 = 0; 
  int fall_11 = 0;

  /*
  Negative monitor will attempt simulation of all 4 SPI types by adjusting:
  1. CPOL: clock signal inversion. 
  2. CPHA: clock phase adjustment (half period faster). 
  */
  task run_phase(uvm_phase phase);
    spi_tran item01L[$], item01T[$], item00L[$], item00T[$], item10L[$], item10T[$], item11L[$], item11T[$]; 
    spi_tran item01t, item00t, item10t, item11t; 
    int cnt00L = 0, cnt00T = 0, cnt01L = 0, cnt01T = 0, cnt10L = 0, cnt10T = 0, cnt11L = 0, cnt11T = 0;
    fork 
      // SPI1: no need for adjustments on clock, mosi sampled on leading-posedge, miso on trailing-negedge
      begin 
        fork 
          forever begin
            @(posedge vif.sclk);  
            item01t = spi_tran::type_id::create("item01t",this);
            item01t.mt = OL0HA1_L;
            item01t.tran_time_start = $time; 
            item01t.mosi = vif.mosi;
            item01t.curr_lead = lead_01++; 
            item01L.push_back(item01t);
            cnt01L++;
            `uvm_info("MON2", $sformatf("OL0HA1: leading posedge sample."), UVM_LOW);
          end        
          forever begin
            @(negedge vif.sclk iff ($time > 0));
            item01t = spi_tran::type_id::create("item01t",this);
            item01t.mt = OL0HA1_T;
            item01t.tran_time_start = $time; 
            item01t.miso = vif.miso;
            item01t.curr_fall = fall_01++; 
            item01T.push_back(item01t);
            cnt01T++;
            `uvm_info("MON2", $sformatf("OL0HA1: trailing negedge sample. %d", cnt01T-1), UVM_LOW);
          end
          forever begin 
            @(posedge vif.done) begin 
              if (cnt01L == 8) begin 
                cnt01L = 0;
                foreach (item01L[cnt01L]) begin
                  mon2_ap.write(item01L[cnt01L]); 
                end
              end 
              else begin 
                cnt01L = 0;
              end
              item01L.delete();
            end
            @(negedge vif.done) begin
              if (cnt01T == 8) begin 
                cnt01T = 0;
                foreach (item01T[cnt01T]) begin
                  mon2_ap.write(item01T[cnt01T]); 
                end
              end 
              else begin 
                cnt01T = 0;
              end
              item01T.delete();
            end 
          end  
        join 
      end
      // SPI0: NOT CHANGING THE CLOCK, mosi and miso both sampled on leading-posedge.
      begin 
        fork 
          // mosi: start posedge, sclk negedge, when start asserted
          forever begin
            fork
              forever begin 
                //if (il == 0) begin
                  @(posedge vif.start);
                  if (!vif.busy) begin 
                    item00t = spi_tran::type_id::create("item00t",this);
                    item00t.mt = OL0HA0_L;
                    item00t.tran_time_start = $time; 
                    item00t.mosi = vif.mosi;
                    item00t.curr_lead = lead_00++; 
                    item00L.push_back(item00t);
                    cnt00L++;
                    `uvm_info("MON2", $sformatf("OL0HA0_L: start posedge sample. %d  AAA", cnt00L), UVM_LOW);
                  //end 
                end
              end
              forever begin 
                @(negedge vif.sclk);
                #1; 
                if (vif.rst_n && !vif.done) begin  
                  item00t = spi_tran::type_id::create("tis",this);
                  item00t.mt = OL0HA0_L;
                  item00t.tran_time_start = $time; 
                  item00t.mosi = vif.mosi;
                  item00t.curr_lead = lead_00++; 
                  item00L.push_back(item00t);
                  cnt00L++;
                  `uvm_info("MON2", $sformatf("OL0HA0_L: trailing negedge sample. %d BBB", cnt00L), UVM_LOW);
                end
              end
            join
          end
          // miso: sclk posedge, when busy asserted
          forever begin
            @(posedge vif.sclk);
            if (vif.rst_n) begin 
              item00t = spi_tran::type_id::create("item00t",this);
              item00t.mt = OL0HA0_T;
              item00t.tran_time_start = $time; 
              item00t.miso = vif.miso;
              item00t.curr_fall = fall_00++; 
              item00T.push_back(item00t);
              cnt00T++;
              `uvm_info("MON2", $sformatf("OL0HA0_T: leading posedge sample. %d", cnt00T), UVM_LOW);
            end
          end
          forever begin 
            @(posedge vif.done) begin 
              if (cnt00L == 8) begin 
                cnt00L = 0;
                foreach (item00L[cnt00L]) begin
                  mon2_ap.write(item00L[cnt00L]); 
                end
              end 
              else begin 
                cnt00L = 0;
              end
              item00L.delete();
              if (cnt00T == 8) begin 
                cnt00T = 0;
                foreach (item00T[cnt00T]) begin
                  mon2_ap.write(item00T[cnt00T]); 
                end
              end 
              else begin 
                cnt00T = 0;
              end
              item00T.delete();
            end 
          end 
        join
      end
      // SPI2: NOT CHANGING THE CLOCK, mosi sampled on falling edge, in this case moved to trailing edge and miso on rising edge, the leading edge. [will cause data mismatch]
      begin 
        fork 
          forever begin
            fork
            forever begin
              @(posedge vif.start);
              #1;
              if (!vif.busy) begin 
                item10t = spi_tran::type_id::create("item10t",this);
                item10t.mt = OL1HA0_L;
                item10t.tran_time_start = $time; 
                item10t.mosi = vif.mosi;
                item10t.curr_lead = lead_10++; 
                item10L.push_back(item10t);
                cnt10L++;
                `uvm_info("MON2", $sformatf("OL1HA0_L: leading posedge sample. SSS"), UVM_LOW);
              end 
            end
            forever begin 
              @(posedge vif.sclk);
              #1;
              if (vif.rst_n && (cnt01L < 8)) begin  
                item10t = spi_tran::type_id::create("item10t",this);
                item10t.mt = OL1HA0_L;
                item10t.tran_time_start = $time; 
                item10t.mosi = vif.mosi;
                item10t.curr_lead = lead_10++; 
                item10L.push_back(item10t);
                cnt10L++;
                `uvm_info("MON2", $sformatf("OL1HA0_L: leading posedge sample. RRRR"), UVM_LOW);
              end
            end
            join
          end
          forever begin
            @(negedge vif.sclk);            
            #1;
            if (vif.rst_n) begin  
              item10t = spi_tran::type_id::create("item10t",this);
              item10t.mt = OL1HA0_T;
              item10t.tran_time_start = $time; 
              item10t.miso = vif.miso;
              item10t.curr_fall = fall_10++; 
              item10T.push_back(item10t);
              cnt10T++;
              `uvm_info("MON2", $sformatf("OL1HA0_T: leading negedge sample."), UVM_LOW);
            end
          end
          forever begin 
            @(posedge vif.done) begin 
              if (cnt10L == 8) begin 
                cnt10L = 0;
                foreach (item10L[cnt10L]) begin
                  mon2_ap.write(item10L[cnt10L]); 
                end
              end 
              else begin 
                cnt10L = 0;
              end
              item10L.delete();
            end
            @(negedge vif.done) begin
              if (cnt10T == 8) begin 
                cnt10T = 0;
                foreach (item10T[cnt10T]) begin
                  mon2_ap.write(item10T[cnt10T]); 
                end
              end 
              else begin 
                cnt10T = 0;
              end
              item10T.delete();
            end 
          end 
        join
      end
      // SPI3: NOT CHANGING THE CLOCK, mosi and miso sampled both on the leading-negedge [will cause data mismatch]
      begin 
        fork 
          forever begin
            @(negedge vif.isclk iff ($time > 0));
            item11t = spi_tran::type_id::create("item11t",this);
            item11t.mt = OL1HA1_L;
            item11t.tran_time_start = $time; 
            item11t.mosi = vif.mosi;
            item11t.curr_lead = lead_11++; 
            item11L.push_back(item11t);
            cnt11L++; 
            `uvm_info("MON2", $sformatf("OL1HA1: leading negedge sample."), UVM_LOW);
          end          
          forever begin
            @(posedge vif.isclk);
            item11t = spi_tran::type_id::create("item11t",this);
            item11t.mt = OL1HA1_T;
            item11t.tran_time_start = $time; 
            item11t.miso = vif.miso;
            item11t.curr_fall = fall_11++; 
            item11T.push_back(item11t);
            cnt11T++;
            `uvm_info("MON2", $sformatf("OL1HA1: trailing posedge sample."), UVM_LOW);
          end
          forever begin 
            @(posedge vif.done) begin 
              if (cnt11L == 8) begin 
                cnt11L = 0;
                foreach (item11L[cnt11L]) begin
                  mon2_ap.write(item11L[cnt11L]); 
                end
              end 
              else begin 
                cnt11L = 0;
              end
              item11L.delete();
              if (cnt11T == 8) begin 
                cnt11T = 0;
                foreach (item11T[cnt11T]) begin
                  mon2_ap.write(item11T[cnt11T]); 
                end
              end 
              else begin 
                cnt11T = 0;
              end
              item11T.delete();
            end 
          end 
        join 
      end
    join
  endtask
endclass
