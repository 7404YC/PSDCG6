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
    fork 
      // SPI1: no need for adjustments on clock, mosi sampled on leading-posedge, miso on trailing-negedge
      begin 
        spi_tran item_l [$], item_t [$];
        int il = 0, it = 0;
        spi_tran tis;
        fork 
          forever begin
            @(posedge vif.sclk);  
            tis = spi_tran::type_id::create("tis",this);
            tis.mt = OL0HA1_L;
            tis.tran_time_start = $time; 
            tis.mosi = vif.mosi;
            tis.curr_lead = lead_01++; 
            item_l.push_back(tis);
            il++;
            `uvm_info("MON2", $sformatf("OL0HA1: leading posedge sample."), UVM_LOW);
          end        
          forever begin
            @(negedge vif.sclk iff ($time > 0));
            tis = spi_tran::type_id::create("tis",this);
            tis.mt = OL0HA1_T;
            tis.tran_time_start = $time; 
            tis.miso = vif.miso;
            tis.curr_fall = fall_01++; 
            item_t.push_back(tis);
            it++;
            `uvm_info("MON2", $sformatf("OL0HA1: trailing negedge sample."), UVM_LOW);
          end
          forever begin 
            @(posedge vif.done) begin 
              if (il == 8) begin 
                il = 0;
                foreach (item_l[il]) begin
                  mon2_ap.write(item_l[il]); 
                end
              end 
              else begin 
                il = 0;
              end
              item_l.delete();
              if (it == 8) begin 
                it = 0;
                foreach (item_t[it]) begin
                  mon2_ap.write(item_t[it]); 
                end
              end 
              else begin 
                it = 0;
              end
              item_t.delete();
            end 
          end  
        join 
      end
      // SPI0: NOT CHANGING THE CLOCK, mosi and miso both sampled on leading-posedge.
      begin 
        spi_tran item_l [$], item_t [$];
        int il = 0, it = 0; 
        spi_tran tis, tise, tisa;
        fork 
          // mosi: start posedge, sclk negedge, when start asserted
          forever begin
            fork
              forever begin 
                //if (il == 0) begin
                  @(posedge vif.start);
                  if (!vif.busy) begin 
                    tisa = spi_tran::type_id::create("tisa",this);
                    tisa.mt = OL0HA0_L;
                    tisa.tran_time_start = $time; 
                    tisa.mosi = vif.mosi;
                    tisa.curr_lead = lead_00++; 
                    item_l.push_back(tisa);
                    il++;
                    `uvm_info("MON2", $sformatf("OL0HA0_L: leading posedge sample. %d  AAA", il), UVM_LOW);
                  //end 
                end
              end
              forever begin 
                @(negedge vif.sclk);
                #1;
                if (vif.rst_n) begin  
                  tise = spi_tran::type_id::create("tis",this);
                  tise.mt = OL0HA0_L;
                  tise.tran_time_start = $time; 
                  tise.mosi = vif.mosi;
                  tise.curr_lead = lead_00++; 
                  item_l.push_back(tise);
                  il++;
                  `uvm_info("MON2", $sformatf("OL0HA0_L: leading posedge sample. %d BBB", il), UVM_LOW);
                end
              end
            join
          end
          // miso: sclk posedge, when busy asserted
          forever begin
            @(posedge vif.sclk);
            if (vif.rst_n) begin 
              tis = spi_tran::type_id::create("tis",this);
              tis.mt = OL0HA0_T;
              tis.tran_time_start = $time; 
              tis.miso = vif.miso;
              tis.curr_fall = fall_00++; 
              item_t.push_back(tis);
              it++;
              `uvm_info("MON2", $sformatf("OL0HA0_T: leading posedge sample. %d", it), UVM_LOW);
            end
          end
          forever begin 
            @(posedge vif.done) begin 
              if (il == 8) begin 
                il = 0;
                foreach (item_l[il]) begin
                  mon2_ap.write(item_l[il]); 
                end
              end 
              else begin 
                il = 0;
              end
              item_l.delete();
              if (it == 8) begin 
                it = 0;
                foreach (item_t[it]) begin
                  mon2_ap.write(item_t[it]); 
                end
              end 
              else begin 
                it = 0;
              end
              item_t.delete();
            end 
          end 
        join
      end
      // SPI2: NOT CHANGING THE CLOCK, mosi sampled on falling edge, in this case moved to trailing edge and miso on rising edge, the leading edge. [will cause data mismatch]
      begin 
        spi_tran item_l [$], item_t [$];
        int il = 0, it = 0; 
        spi_tran tis;
        fork 
          forever begin
            fork
            forever begin
              @(posedge vif.start);
              #1;
              if (!vif.busy) begin 
                tis = spi_tran::type_id::create("tis",this);
                tis.mt = OL1HA0_L;
                tis.tran_time_start = $time; 
                tis.mosi = vif.mosi;
                tis.curr_lead = lead_10++; 
                item_l.push_back(tis);
                il++;
                `uvm_info("MON2", $sformatf("OL1HA0_L: leading posedge sample."), UVM_LOW);
              end 
            end
            forever begin 
              @(posedge vif.sclk);
              #1;
              if (vif.rst_n) begin  
                tis = spi_tran::type_id::create("tis",this);
                tis.mt = OL1HA0_L;
                tis.tran_time_start = $time; 
                tis.mosi = vif.mosi;
                tis.curr_lead = lead_10++; 
                item_l.push_back(tis);
                il++;
                `uvm_info("MON2", $sformatf("OL1HA0_L: leading posedge sample."), UVM_LOW);
              end
            end
            join
          end
          forever begin
            @(negedge vif.sclk);            
            #1;
            if (vif.rst_n) begin  
              tis = spi_tran::type_id::create("tis",this);
              tis.mt = OL1HA0_T;
              tis.tran_time_start = $time; 
              tis.miso = vif.miso;
              tis.curr_fall = fall_10++; 
              item_t.push_back(tis);
              it++;
              `uvm_info("MON2", $sformatf("OL1HA0_T: leading negedge sample."), UVM_LOW);
            end
          end
          forever begin 
            @(posedge vif.done) begin 
              if (il == 8) begin 
                il = 0;
                foreach (item_l[il]) begin
                  mon2_ap.write(item_l[il]); 
                end
              end 
              else begin 
                il = 0;
              end
              item_l.delete();
              if (it == 8) begin 
                it = 0;
                foreach (item_t[it]) begin
                  mon2_ap.write(item_t[it]); 
                end
              end 
              else begin 
                it = 0;
              end
              item_t.delete();
            end 
          end 
        join
      end
      // SPI3: NOT CHANGING THE CLOCK, mosi and miso sampled both on the leading-negedge [will cause data mismatch]
      begin 
        spi_tran item_l [$], item_t [$];
        int il = 0, it = 0; 
        spi_tran tis;

        fork 
          forever begin
            @(negedge vif.isclk iff ($time > 0));
            tis = spi_tran::type_id::create("tis",this);
            tis.mt = OL1HA1_L;
            tis.tran_time_start = $time; 
            tis.mosi = vif.mosi;
            tis.curr_lead = lead_11++; 
            item_l.push_back(tis);
            il++; 
            `uvm_info("MON2", $sformatf("OL1HA1: leading negedge sample."), UVM_LOW);
          end          
          forever begin
            @(posedge vif.isclk);
            tis = spi_tran::type_id::create("tis",this);
            tis.mt = OL1HA1_T;
            tis.tran_time_start = $time; 
            tis.miso = vif.miso;
            tis.curr_fall = fall_11++; 
            item_t.push_back(tis);
            it++;
            `uvm_info("MON2", $sformatf("OL1HA1: trailing posedge sample."), UVM_LOW);
          end
          forever begin 
            @(posedge vif.done) begin 
              if (il == 8) begin 
                il = 0;
                foreach (item_l[il]) begin
                  mon2_ap.write(item_l[il]); 
                end
              end 
              else begin 
                il = 0;
              end
              item_l.delete();
              if (it == 8) begin 
                it = 0;
                foreach (item_t[it]) begin
                  mon2_ap.write(item_t[it]); 
                end
              end 
              else begin 
                it = 0;
              end
              item_t.delete();
            end 
          end 
        join 
      end
    join
  endtask
endclass
