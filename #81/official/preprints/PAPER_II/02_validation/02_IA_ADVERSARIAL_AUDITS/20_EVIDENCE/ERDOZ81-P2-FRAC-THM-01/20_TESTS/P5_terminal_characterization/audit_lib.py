"""
audit_lib.py  --  shared helpers for the ERDOS81 external adversarial audit.

Provides:
  * build_pdf(path, title, meta, sections): render an English PDF report with
    reportlab (no external LaTeX needed).
  * package(folder, zip_basename, files): create a zip of the given files and a
    matching .sha256 file for the zip.

This module is COPIED into every test folder so each folder + zip is a
self-contained, independently reproducible artifact.
"""
import os
import zipfile
import hashlib

from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import cm
from reportlab.lib import colors
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, Preformatted,
)


def _styles():
    ss = getSampleStyleSheet()
    ss.add(ParagraphStyle(name="Mono", fontName="Courier", fontSize=7.5,
                          leading=9.5))
    ss.add(ParagraphStyle(name="H1b", parent=ss["Heading1"], fontSize=15,
                          spaceBefore=6, spaceAfter=8))
    ss.add(ParagraphStyle(name="H2b", parent=ss["Heading2"], fontSize=11.5,
                          spaceBefore=10, spaceAfter=4))
    ss.add(ParagraphStyle(name="Body", parent=ss["BodyText"], fontSize=9.5,
                          leading=13, spaceAfter=5))
    ss.add(ParagraphStyle(name="Small", parent=ss["BodyText"], fontSize=8,
                          leading=10, textColor=colors.grey))
    return ss


def build_pdf(path, title, meta, sections):
    """
    meta: list of (label, value) shown in a header box.
    sections: list of dicts, each one of:
        {"h": "Heading"}                              -> section heading
        {"p": "paragraph text"}                       -> body paragraph
        {"code": "monospace block"}                   -> preformatted block
        {"table": [[r0c0, r0c1], ...], "header": T/F} -> table (row 0 = header)
    """
    ss = _styles()
    doc = SimpleDocTemplate(path, pagesize=LETTER,
                            leftMargin=1.8 * cm, rightMargin=1.8 * cm,
                            topMargin=1.6 * cm, bottomMargin=1.6 * cm,
                            title=title)
    story = []
    story.append(Paragraph(title, ss["H1b"]))
    if meta:
        mt = Table([[Paragraph(f"<b>{k}</b>", ss["Small"]),
                     Paragraph(str(v), ss["Small"])] for k, v in meta],
                   colWidths=[4.5 * cm, 12.5 * cm])
        mt.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, -1), colors.whitesmoke),
            ("BOX", (0, 0), (-1, -1), 0.4, colors.grey),
            ("INNERGRID", (0, 0), (-1, -1), 0.25, colors.lightgrey),
            ("VALIGN", (0, 0), (-1, -1), "TOP"),
            ("TOPPADDING", (0, 0), (-1, -1), 2),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 2),
        ]))
        story.append(mt)
        story.append(Spacer(1, 8))

    for sec in sections:
        if "h" in sec:
            story.append(Paragraph(sec["h"], ss["H2b"]))
        if "p" in sec:
            story.append(Paragraph(sec["p"], ss["Body"]))
        if "code" in sec:
            story.append(Preformatted(sec["code"], ss["Mono"]))
            story.append(Spacer(1, 4))
        if "table" in sec:
            data = sec["table"]
            wrap = sec.get("wrap", False)
            if wrap:
                data = [[Paragraph(str(c), ss["Small"]) for c in row]
                        for row in data]
            t = Table(data, repeatRows=1, colWidths=sec.get("colWidths"))
            tstyle = [
                ("BOX", (0, 0), (-1, -1), 0.4, colors.grey),
                ("INNERGRID", (0, 0), (-1, -1), 0.25, colors.lightgrey),
                ("FONTSIZE", (0, 0), (-1, -1), 7.5),
                ("VALIGN", (0, 0), (-1, -1), "TOP"),
                ("TOPPADDING", (0, 0), (-1, -1), 2),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 2),
            ]
            if sec.get("header", True):
                tstyle += [
                    ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#2b3a55")),
                    ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
                    ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
                ]
            t.setStyle(TableStyle(tstyle))
            story.append(t)
            story.append(Spacer(1, 6))

    doc.build(story)
    return path


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def package(folder, zip_basename, files):
    """Zip `files` (relative to folder) into folder/zip_basename.zip and write
    folder/zip_basename.zip.sha256 . Returns (zip_path, sha_path, digest)."""
    zip_path = os.path.join(folder, zip_basename + ".zip")
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as z:
        for fn in files:
            full = os.path.join(folder, fn)
            if os.path.exists(full):
                z.write(full, arcname=fn)
    digest = sha256_of(zip_path)
    sha_path = zip_path + ".sha256"
    # newline="" avoids Windows CRLF translation so `sha256sum -c` accepts the file
    with open(sha_path, "w