class RDL::Verify
  
  def self.inst_hash_dispatch(meth_name)
    case meth_name
    when :[]
        ["hash_ref", false]
    when :[]=
        ["hash_asgn", false]
    when :each
      ["hash_each", true]
    when :length, :size
      ["hash_length", false]
    else
      #raise RuntimeError, "unsupported Hash method #{meth_name}"
      ## should only reach this case when user has defined their own Hash method
      #meths << ["Hash", meth, true]
      ["Hash_inst_#{meth}", true]
    end
  end

end
