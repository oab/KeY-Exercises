package unionfind;

public interface Element {
    public int getSize();
    public int getName();
    public Element findRoot();
    public void union(Element e);
}
